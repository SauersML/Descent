/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Foundations.Probability
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fintype.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent.Blindness
namespace NormVisibility

open Filter Topology

/-!
# Norm visibility: the size a perturbation has depends on which norm reads it

A perturbation of a population — a subgroup whose calibration is wrong, a stratum whose
ancestry is misassigned, a handful of variants whose effects are mis-signed — has two
sizes, and they are not the same number. The **worst-case** size is the largest error any
one individual carries. The **mean-square** size is the error a population-average
statistic reports. This file proves the one inequality relating them, and shows that it is
the only relation there is: the gap between the two sizes is exactly the fraction of the
population the perturbation touches.

## The inequality

`rootMeanSquare_le_of_support` — a perturbation supported on at most `budget` of the
`Fintype.card Coordinate` coordinates has

    root-mean-square size  ≤  √(budget / coordinates) × worst-case size.

Nothing else is needed: not a distributional assumption, not independence, not a limit.
It is the Cauchy-Schwarz counting bound and it is tight at both ends, which is what makes
it a statement about probes rather than a technical estimate.

## Both ends are attained, and that is the content

`localizedFamily` puts unit amplitude on one coordinate: worst case `1`, mean square
`1/√n`. `denseFamily` puts unit amplitude on every coordinate: worst case `1`, mean square
`1`. So over a sequence of growing populations the first is invisible to any mean-square
probe while remaining fully visible to a worst-case one, and the second is visible to
both. `exists_worstCaseVisible_and_not_meanSquareVisible` is the strictness statement and
`worstCaseVisible_of_meanSquareVisible` is the implication that does hold, with its
constant.

## Why a polygenic-score development states this

The population-average performance of a score — incremental R², average calibration slope,
mean absolute error — is a mean-square probe. `worstCase_survives_while_meanSquare_vanishes`
says that a subpopulation of vanishing relative size can carry order-one per-individual
error while every such average converges to the unperturbed value. The average is not
approximately right about that subgroup; it is exactly uninformative about it, and no
amount of sample size changes the arithmetic, because the sample size is the `n` in the
denominator. That is the blindness this file supplies to the `Descent.Portability`
calibration vocabulary (`ContinuumCalibration.calibrationDriftDefectSq`,
`PortabilityMasterTheorem.calibrationSlope`): those quantities are pooled second moments,
so they inherit the `√(budget / coordinates)` discount on everything a minority carries.
The corollary is stated here rather than there because this file sits below
`Descent.Portability` in the layer order.

## What this file does not say

It does not say a small subgroup is *always* invisible: `supportVisible_of_meanSquareVisible`
runs the inequality backwards and shows that a mean-square-visible perturbation with
bounded amplitude must touch an order-one fraction of the population. Visibility in the
average is equivalent to breadth, given an amplitude ceiling. The one-sided reading — that
averages hide minorities — is the case where the ceiling is real; where per-individual
error may grow, a shrinking subgroup can still move the average, and the inequality says
by how much.
-/

/-! ## 1. The two sizes -/

/-- The **mean-square size** of a perturbation: its Euclidean norm divided by the square
root of the number of coordinates, so that a perturbation of constant amplitude has this
size equal to that amplitude regardless of how many coordinates there are. This is the
size a population-average second-moment statistic reports.

With no coordinates the division is by zero and Mathlib returns `0`; there is no mean
square of an empty population, and `rootMeanSquare_of_isEmpty` records the junk value
rather than leaving it to be discovered. -/
noncomputable def rootMeanSquare {Coordinate : Type*} [Fintype Coordinate]
    (perturbation : Coordinate → ℝ) : ℝ :=
  Real.sqrt ((∑ coordinate, perturbation coordinate ^ 2) / (Fintype.card Coordinate : ℝ))

/-- The **worst-case size** of a perturbation: the largest absolute coordinate. This is
the size a per-individual audit reports.

With no coordinates the supremum is over an empty family and Mathlib returns `0`. -/
noncomputable def supremumNorm {Coordinate : Type*} [Fintype Coordinate]
    (perturbation : Coordinate → ℝ) : ℝ :=
  ⨆ coordinate, |perturbation coordinate|

/-- The number of coordinates a perturbation actually moves. -/
noncomputable def supportSize {Coordinate : Type*} [Fintype Coordinate]
    (perturbation : Coordinate → ℝ) : ℕ :=
  (Function.support perturbation).ncard

/-- On an empty coordinate type the mean square divides by zero and reports `0`. -/
theorem rootMeanSquare_of_isEmpty {Coordinate : Type*} [Fintype Coordinate]
    [IsEmpty Coordinate] (perturbation : Coordinate → ℝ) :
    rootMeanSquare perturbation = 0 := by
  simp [rootMeanSquare]

/-- On an empty coordinate type the worst case is a supremum over nothing and reports `0`. -/
theorem supremumNorm_of_isEmpty {Coordinate : Type*} [Fintype Coordinate]
    [IsEmpty Coordinate] (perturbation : Coordinate → ℝ) :
    supremumNorm perturbation = 0 := by
  simp [supremumNorm]

/-- The mean square is a square root, hence nonnegative. -/
theorem rootMeanSquare_nonneg {Coordinate : Type*} [Fintype Coordinate]
    (perturbation : Coordinate → ℝ) : 0 ≤ rootMeanSquare perturbation :=
  Real.sqrt_nonneg _

/-- The worst case dominates every single coordinate. -/
theorem le_supremumNorm {Coordinate : Type*} [Fintype Coordinate]
    (perturbation : Coordinate → ℝ) (coordinate : Coordinate) :
    |perturbation coordinate| ≤ supremumNorm perturbation := by
  unfold supremumNorm
  exact le_ciSup (Finite.bddAbove_range fun site ↦ |perturbation site|) coordinate

/-- The worst case is nonnegative, including on an empty coordinate type. -/
theorem supremumNorm_nonneg {Coordinate : Type*} [Fintype Coordinate]
    (perturbation : Coordinate → ℝ) : 0 ≤ supremumNorm perturbation :=
  Real.iSup_nonneg fun _coordinate ↦ abs_nonneg _

/-- A uniform coordinate bound bounds the worst case. The nonnegativity premise is what
covers the empty coordinate type, where the supremum is `0` and the coordinate hypothesis
says nothing. -/
theorem supremumNorm_le {Coordinate : Type*} [Fintype Coordinate]
    (perturbation : Coordinate → ℝ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hcoordinates : ∀ coordinate, |perturbation coordinate| ≤ bound) :
    supremumNorm perturbation ≤ bound := by
  rcases isEmpty_or_nonempty Coordinate with hempty | hnonempty
  · haveI := hempty
    simpa [supremumNorm] using hbound
  · exact ciSup_le hcoordinates

/-! ## 2. The visibility inequality -/

/-- **The visibility inequality.** A perturbation vanishing off a set of at most `budget`
coordinates has mean-square size at most `√(budget / coordinates)` times its worst-case
size.

This is the whole mechanism of the file. The support hypothesis is `Finset`-level and
carries no structure beyond its cardinality: what the bound charges is the number of
coordinates that may be nonzero, not which ones or how they are arranged. -/
theorem rootMeanSquare_le_of_support {Coordinate : Type*} [Fintype Coordinate]
    (perturbation : Coordinate → ℝ) (support : Finset Coordinate) (budget : ℕ)
    (hoff : ∀ coordinate ∉ support, perturbation coordinate = 0)
    (hbudget : support.card ≤ budget)
    (worstCase : ℝ) (hworstCase : ∀ coordinate, |perturbation coordinate| ≤ worstCase) :
    rootMeanSquare perturbation
      ≤ Real.sqrt ((budget : ℝ) / (Fintype.card Coordinate : ℝ)) * worstCase := by
  rcases isEmpty_or_nonempty Coordinate with hempty | hnonempty
  · haveI := hempty
    simp [rootMeanSquare]
  · obtain ⟨witness⟩ := hnonempty
    have hnonneg : 0 ≤ worstCase := le_trans (abs_nonneg _) (hworstCase witness)
    have hrestrict : ∑ coordinate ∈ support, perturbation coordinate ^ 2
        = ∑ coordinate, perturbation coordinate ^ 2 := by
      refine Finset.sum_subset (Finset.subset_univ support) ?_
      intro coordinate _hmem hnot
      rw [hoff coordinate hnot]
      ring
    have hterms : ∑ coordinate ∈ support, perturbation coordinate ^ 2
        ≤ support.card • worstCase ^ 2 := by
      refine Finset.sum_le_card_nsmul _ _ _ ?_
      intro coordinate _hmem
      have hsquare : |perturbation coordinate| ^ 2 ≤ worstCase ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hworstCase coordinate) 2
      simpa [sq_abs] using hsquare
    have hsum : ∑ coordinate, perturbation coordinate ^ 2 ≤ (budget : ℝ) * worstCase ^ 2 := by
      rw [← hrestrict]
      refine hterms.trans ?_
      rw [nsmul_eq_mul]
      have hcast : (support.card : ℝ) ≤ (budget : ℝ) := by exact_mod_cast hbudget
      have hsquare : (0 : ℝ) ≤ worstCase ^ 2 := sq_nonneg _
      exact mul_le_mul_of_nonneg_right hcast hsquare
    have hdivide : (∑ coordinate, perturbation coordinate ^ 2) / (Fintype.card Coordinate : ℝ)
        ≤ (budget : ℝ) * worstCase ^ 2 / (Fintype.card Coordinate : ℝ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hsum (by positivity)
    calc rootMeanSquare perturbation
        ≤ Real.sqrt ((budget : ℝ) * worstCase ^ 2 / (Fintype.card Coordinate : ℝ)) :=
          Real.sqrt_le_sqrt hdivide
      _ = Real.sqrt ((budget : ℝ) / (Fintype.card Coordinate : ℝ) * worstCase ^ 2) := by
          rw [div_mul_eq_mul_div]
      _ = Real.sqrt ((budget : ℝ) / (Fintype.card Coordinate : ℝ)) * worstCase := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hnonneg]

/-- The inequality read against the perturbation's own worst case. -/
theorem rootMeanSquare_le_supremumNorm_of_support {Coordinate : Type*} [Fintype Coordinate]
    (perturbation : Coordinate → ℝ) (support : Finset Coordinate) (budget : ℕ)
    (hoff : ∀ coordinate ∉ support, perturbation coordinate = 0)
    (hbudget : support.card ≤ budget) :
    rootMeanSquare perturbation
      ≤ Real.sqrt ((budget : ℝ) / (Fintype.card Coordinate : ℝ)) * supremumNorm perturbation :=
  rootMeanSquare_le_of_support perturbation support budget hoff hbudget
    (supremumNorm perturbation) (le_supremumNorm perturbation)

/-- The inequality at full support: the mean square never exceeds the worst case. The
discount factor is `√(n/n) = 1`, so this is the one instance in which the counting bound
gives nothing away, and every family attaining it is dense. -/
theorem rootMeanSquare_le_supremumNorm {Coordinate : Type*} [Fintype Coordinate]
    (perturbation : Coordinate → ℝ) :
    rootMeanSquare perturbation ≤ supremumNorm perturbation := by
  rcases isEmpty_or_nonempty Coordinate with hempty | hnonempty
  · haveI := hempty
    simp [rootMeanSquare, supremumNorm]
  · have hcard : (0 : ℝ) < (Fintype.card Coordinate : ℝ) := by
      exact_mod_cast Fintype.card_pos
    have hmain := rootMeanSquare_le_supremumNorm_of_support perturbation Finset.univ
      (Fintype.card Coordinate) (by simp) (by simp)
    rwa [div_self hcard.ne', Real.sqrt_one, one_mul] at hmain

/-- The inequality with the perturbation's actual support in place of a budget. -/
theorem rootMeanSquare_le_supportSize {Coordinate : Type*} [Fintype Coordinate]
    (perturbation : Coordinate → ℝ) (worstCase : ℝ)
    (hworstCase : ∀ coordinate, |perturbation coordinate| ≤ worstCase) :
    rootMeanSquare perturbation
      ≤ Real.sqrt ((supportSize perturbation : ℝ) / (Fintype.card Coordinate : ℝ)) * worstCase := by
  classical
  have hsupport : Function.support perturbation
      = ↑(Finset.univ.filter fun coordinate ↦ perturbation coordinate ≠ 0) := by
    ext coordinate
    simp [Function.mem_support]
  have hcard : supportSize perturbation
      = (Finset.univ.filter fun coordinate ↦ perturbation coordinate ≠ 0).card := by
    rw [supportSize, hsupport, Set.ncard_coe_finset]
  refine rootMeanSquare_le_of_support perturbation
    (Finset.univ.filter fun coordinate ↦ perturbation coordinate ≠ 0)
    (supportSize perturbation) ?_ (le_of_eq hcard.symm) worstCase hworstCase
  intro coordinate hcoordinate
  simpa using hcoordinate

/-- **The inequality run backwards.** A perturbation whose amplitude is capped must touch
at least `(mean square / cap)²` of the population to reach its mean-square size. Breadth is
not merely sufficient for visibility in an average; given a ceiling on per-individual size,
it is necessary. -/
theorem supportSize_ge_of_rootMeanSquare {Coordinate : Type*} [Fintype Coordinate]
    (perturbation : Coordinate → ℝ) (amplitude : ℝ) (hamplitude : 0 < amplitude)
    (hbounded : ∀ coordinate, |perturbation coordinate| ≤ amplitude) :
    (rootMeanSquare perturbation / amplitude) ^ 2 * (Fintype.card Coordinate : ℝ)
      ≤ (supportSize perturbation : ℝ) := by
  have hmain := rootMeanSquare_le_supportSize perturbation amplitude hbounded
  have hfraction : (0 : ℝ)
      ≤ (supportSize perturbation : ℝ) / (Fintype.card Coordinate : ℝ) := by positivity
  have hratio : rootMeanSquare perturbation / amplitude
      ≤ Real.sqrt ((supportSize perturbation : ℝ) / (Fintype.card Coordinate : ℝ)) := by
    rw [div_le_iff₀ hamplitude]
    exact hmain
  have hsquare : (rootMeanSquare perturbation / amplitude) ^ 2
      ≤ (supportSize perturbation : ℝ) / (Fintype.card Coordinate : ℝ) := by
    calc (rootMeanSquare perturbation / amplitude) ^ 2
        ≤ Real.sqrt ((supportSize perturbation : ℝ) / (Fintype.card Coordinate : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (div_nonneg (rootMeanSquare_nonneg _) hamplitude.le) hratio 2
      _ = (supportSize perturbation : ℝ) / (Fintype.card Coordinate : ℝ) :=
          Real.sq_sqrt hfraction
  rcases Nat.eq_zero_or_pos (Fintype.card Coordinate) with hzero | hpositive
  · rw [hzero]
    simp
  · have hcard : (0 : ℝ) < (Fintype.card Coordinate : ℝ) := by exact_mod_cast hpositive
    rw [← le_div_iff₀ hcard]
    exact hsquare

/-! ## 3. The two extremal families

Both families have worst-case size one at every dimension. They differ only in how many
coordinates carry it, and that difference is the entire gap in the inequality. -/

/-- The **localized family**: unit amplitude on the first coordinate, zero elsewhere. At
dimension zero it is the empty function, which is the honest reading — there is no first
coordinate — and the statements below all carry a positivity premise. -/
noncomputable def localizedFamily (dimension : ℕ) : Fin dimension → ℝ :=
  fun coordinate ↦ if (coordinate : ℕ) = 0 then 1 else 0

/-- The **dense family**: unit amplitude on every coordinate. -/
noncomputable def denseFamily (dimension : ℕ) : Fin dimension → ℝ :=
  fun _coordinate ↦ 1

/-- The localized family is supported on the single first coordinate. -/
theorem localizedFamily_eq_zero_of_ne {dimension : ℕ} (coordinate : Fin dimension)
    (hcoordinate : (coordinate : ℕ) ≠ 0) : localizedFamily dimension coordinate = 0 := by
  simp [localizedFamily, hcoordinate]

/-- The worst-case size of the localized family is exactly one. -/
theorem supremumNorm_localizedFamily (dimension : ℕ) (hdimension : 0 < dimension) :
    supremumNorm (localizedFamily dimension) = 1 := by
  refine le_antisymm (supremumNorm_le _ 1 zero_le_one ?_) ?_
  · intro coordinate
    unfold localizedFamily
    split <;> norm_num
  · have hfirst : localizedFamily dimension ⟨0, hdimension⟩ = 1 := by
      simp [localizedFamily]
    calc (1 : ℝ) = |localizedFamily dimension ⟨0, hdimension⟩| := by rw [hfirst]; norm_num
      _ ≤ supremumNorm (localizedFamily dimension) := le_supremumNorm _ _

/-- **The mean-square size of the localized family is exactly `1 / √n`.** One individual
carrying a full unit of error registers, in a population average, as an error of one over
the square root of the population size. -/
theorem rootMeanSquare_localizedFamily (dimension : ℕ) (hdimension : 0 < dimension) :
    rootMeanSquare (localizedFamily dimension) = 1 / Real.sqrt (dimension : ℝ) := by
  obtain ⟨predecessor, rfl⟩ : ∃ predecessor : ℕ, dimension = predecessor + 1 :=
    ⟨dimension - 1, (Nat.succ_pred_eq_of_pos hdimension).symm⟩
  have hterms : ∀ coordinate : Fin (predecessor + 1),
      localizedFamily (predecessor + 1) coordinate ^ 2
        = if (coordinate : ℕ) = 0 then (1 : ℝ) else 0 := by
    intro coordinate
    unfold localizedFamily
    split <;> norm_num
  have hsum : ∑ coordinate, localizedFamily (predecessor + 1) coordinate ^ 2 = 1 := by
    rw [Finset.sum_congr rfl fun coordinate _hcoordinate ↦ hterms coordinate]
    simp [Fin.val_eq_zero_iff]
  rw [rootMeanSquare, hsum, Fintype.card_fin, Real.sqrt_div zero_le_one, Real.sqrt_one]

/-- The worst-case size of the dense family is exactly one. -/
theorem supremumNorm_denseFamily (dimension : ℕ) (hdimension : 0 < dimension) :
    supremumNorm (denseFamily dimension) = 1 := by
  haveI : Nonempty (Fin dimension) := ⟨⟨0, hdimension⟩⟩
  refine le_antisymm (supremumNorm_le _ 1 zero_le_one ?_) ?_
  · intro coordinate
    simp [denseFamily]
  · calc (1 : ℝ) = |denseFamily dimension ⟨0, hdimension⟩| := by simp [denseFamily]
      _ ≤ supremumNorm (denseFamily dimension) := le_supremumNorm _ _

/-- The mean-square size of the dense family is exactly one: it saturates
`rootMeanSquare_le_supremumNorm`, and so is what an average sees in full. -/
theorem rootMeanSquare_denseFamily (dimension : ℕ) (hdimension : 0 < dimension) :
    rootMeanSquare (denseFamily dimension) = 1 := by
  have hcast : ((dimension : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdimension.ne'
  unfold rootMeanSquare denseFamily
  simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  rw [div_self hcast, Real.sqrt_one]

/-- The dense family moves every coordinate. -/
theorem supportSize_denseFamily (dimension : ℕ) :
    supportSize (denseFamily dimension) = dimension := by
  have hsupport : Function.support (denseFamily dimension) = Set.univ := by
    ext coordinate
    simp [denseFamily, Function.mem_support]
  rw [supportSize, hsupport, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ## 4. The vocabulary

A **family** here is a perturbation at each dimension, and the question is what survives as
the dimension grows. Each predicate asks for a fixed positive floor that the family's size
clears at every large dimension; the three differ only in which size is measured. -/

/-- A family is **worst-case visible** when some fixed positive amplitude survives in its
largest coordinate at every large dimension: a per-individual audit keeps finding it. -/
def WorstCaseVisible (family : ∀ dimension : ℕ, Fin dimension → ℝ) : Prop :=
  ∃ floor : ℝ, 0 < floor ∧ ∀ᶠ dimension in atTop, floor ≤ supremumNorm (family dimension)

/-- A family is **mean-square visible** when some fixed positive amplitude survives in its
population average at every large dimension: a pooled second-moment statistic keeps finding
it. -/
def MeanSquareVisible (family : ∀ dimension : ℕ, Fin dimension → ℝ) : Prop :=
  ∃ floor : ℝ, 0 < floor ∧ ∀ᶠ dimension in atTop, floor ≤ rootMeanSquare (family dimension)

/-- A family is **support visible** when it moves a fixed positive fraction of the
coordinates at every large dimension: it is broad, whatever its amplitude. -/
def SupportVisible (family : ∀ dimension : ℕ, Fin dimension → ℝ) : Prop :=
  ∃ fraction : ℝ, 0 < fraction ∧ ∀ᶠ dimension : ℕ in atTop,
    fraction * (dimension : ℝ) ≤ (supportSize (family dimension) : ℝ)

/-- The localized family is worst-case visible: the witness that the predicate is not
empty, and the family that separates it from the other two. -/
theorem worstCaseVisible_localizedFamily : WorstCaseVisible localizedFamily := by
  refine ⟨1, zero_lt_one, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with dimension hdimension
  rw [supremumNorm_localizedFamily dimension hdimension]

/-- The dense family is mean-square visible: the witness for that predicate. -/
theorem meanSquareVisible_denseFamily : MeanSquareVisible denseFamily := by
  refine ⟨1, zero_lt_one, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with dimension hdimension
  rw [rootMeanSquare_denseFamily dimension hdimension]

/-- The dense family is support visible: the witness for that predicate. -/
theorem supportVisible_denseFamily : SupportVisible denseFamily := by
  refine ⟨1, zero_lt_one, Filter.Eventually.of_forall fun dimension : ℕ ↦ ?_⟩
  rw [supportSize_denseFamily dimension, one_mul]

/-- **Mean-square visibility implies worst-case visibility, with the same floor.** The
constant is one: by `rootMeanSquare_le_supremumNorm` the average never exceeds the worst
case, so any floor the average clears the worst case clears too. -/
theorem worstCaseVisible_of_meanSquareVisible (family : ∀ dimension : ℕ, Fin dimension → ℝ)
    (hvisible : MeanSquareVisible family) : WorstCaseVisible family := by
  obtain ⟨floor, hfloor, hbound⟩ := hvisible
  refine ⟨floor, hfloor, ?_⟩
  filter_upwards [hbound] with dimension hdimension
  exact hdimension.trans (rootMeanSquare_le_supremumNorm (family dimension))

/-- **Mean-square visibility implies support visibility, under an amplitude ceiling.** The
fraction is `(floor / amplitude)²`, from `supportSize_ge_of_rootMeanSquare`: to move a
pooled average by `floor` with no individual moving more than `amplitude`, that fraction of
the population must be touched. -/
theorem supportVisible_of_meanSquareVisible (family : ∀ dimension : ℕ, Fin dimension → ℝ)
    (amplitude : ℝ) (hamplitude : 0 < amplitude)
    (hbounded : ∀ dimension coordinate, |family dimension coordinate| ≤ amplitude)
    (hvisible : MeanSquareVisible family) : SupportVisible family := by
  obtain ⟨floor, hfloor, hbound⟩ := hvisible
  refine ⟨(floor / amplitude) ^ 2, pow_pos (div_pos hfloor hamplitude) 2, ?_⟩
  filter_upwards [hbound] with dimension hdimension
  have hmain := supportSize_ge_of_rootMeanSquare (family dimension) amplitude hamplitude
    (hbounded dimension)
  refine le_trans ?_ (by simpa [Fintype.card_fin] using hmain)
  have hratio : floor / amplitude ≤ rootMeanSquare (family dimension) / amplitude := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hdimension (inv_nonneg.mpr hamplitude.le)
  have hsquare : (floor / amplitude) ^ 2
      ≤ (rootMeanSquare (family dimension) / amplitude) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg hfloor.le hamplitude.le) hratio 2
  exact mul_le_mul_of_nonneg_right hsquare (Nat.cast_nonneg dimension)

/-! ## 5. Vanishing support, and what a population average cannot see -/

/-- **A perturbation on a vanishing fraction of the population is invisible in the
average.** The amplitude ceiling is uniform in the dimension, so the entire effect is the
support fraction: the mean-square size is squeezed by `√(fraction) × amplitude`. -/
theorem tendsto_rootMeanSquare_of_supportFraction_tendsto_zero
    (family : ∀ dimension : ℕ, Fin dimension → ℝ) (budget : ℕ → ℕ) (amplitude : ℝ)
    (hsupport : ∀ dimension : ℕ, ∃ support : Finset (Fin dimension),
      support.card ≤ budget dimension ∧
        ∀ coordinate ∉ support, family dimension coordinate = 0)
    (hbounded : ∀ dimension coordinate, |family dimension coordinate| ≤ amplitude)
    (hfraction : Tendsto (fun dimension : ℕ ↦ (budget dimension : ℝ) / (dimension : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun dimension : ℕ ↦ rootMeanSquare (family dimension)) atTop (𝓝 0) := by
  have hupper : ∀ dimension : ℕ, rootMeanSquare (family dimension)
      ≤ Real.sqrt ((budget dimension : ℝ) / (dimension : ℝ)) * amplitude := by
    intro dimension
    obtain ⟨support, hcard, hoff⟩ := hsupport dimension
    have hmain := rootMeanSquare_le_of_support (family dimension) support (budget dimension)
      hoff hcard amplitude (hbounded dimension)
    simpa [Fintype.card_fin] using hmain
  have hlimit : Tendsto
      (fun dimension : ℕ ↦ Real.sqrt ((budget dimension : ℝ) / (dimension : ℝ)) * amplitude)
      atTop (𝓝 0) := by
    have hsqrt := hfraction.sqrt
    rw [Real.sqrt_zero] at hsqrt
    simpa using hsqrt.mul_const amplitude
  exact squeeze_zero (fun dimension ↦ rootMeanSquare_nonneg (family dimension)) hupper hlimit

/-- The localized family's mean-square size vanishes: it is the case `budget = 1` of the
theorem above, with `1 / n → 0` supplying the vanishing fraction. -/
theorem tendsto_rootMeanSquare_localizedFamily :
    Tendsto (fun dimension : ℕ ↦ rootMeanSquare (localizedFamily dimension)) atTop (𝓝 0) := by
  refine tendsto_rootMeanSquare_of_supportFraction_tendsto_zero localizedFamily
    (fun _dimension ↦ 1) 1 ?_ ?_ ?_
  · intro dimension
    refine ⟨Finset.univ.filter fun coordinate ↦ (coordinate : ℕ) = 0, ?_, ?_⟩
    · rw [Finset.card_le_one]
      intro first hfirst second hsecond
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hfirst hsecond
      exact Fin.val_injective (hfirst.trans hsecond.symm)
    · intro coordinate hcoordinate
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcoordinate
      exact localizedFamily_eq_zero_of_ne coordinate hcoordinate
  · intro dimension coordinate
    unfold localizedFamily
    split <;> norm_num
  · simpa using tendsto_one_div_atTop_nhds_zero_nat

/-- **The localized family is worst-case visible and not mean-square visible.** A floor the
average clears cannot exist, because the average tends to zero — which is the exact sense in
which the implication `worstCaseVisible_of_meanSquareVisible` does not reverse. -/
theorem not_meanSquareVisible_localizedFamily : ¬ MeanSquareVisible localizedFamily := by
  rintro ⟨floor, hfloor, hbound⟩
  have hsmall : ∀ᶠ dimension in atTop,
      rootMeanSquare (localizedFamily dimension) < floor :=
    tendsto_rootMeanSquare_localizedFamily.eventually (gt_mem_nhds hfloor)
  obtain ⟨dimension, hlower, hupper⟩ := (hbound.and hsmall).exists
  exact absurd hlower (not_le.mpr hupper)

/-- **The strictness statement.** Worst-case visibility does not imply mean-square
visibility: the localized family carries a full unit of error at one individual forever,
and every population average of it converges to zero. -/
theorem exists_worstCaseVisible_and_not_meanSquareVisible :
    ∃ family : ∀ dimension : ℕ, Fin dimension → ℝ,
      WorstCaseVisible family ∧ ¬ MeanSquareVisible family :=
  ⟨localizedFamily, worstCaseVisible_localizedFamily, not_meanSquareVisible_localizedFamily⟩

/-- **The reading this file exists for.** A subpopulation of vanishing relative size can
carry order-one per-individual error while every population-average measure of that error
converges to zero. The two conclusions are simultaneous and neither is an approximation:
the worst case stays pinned at one and the average is a limit of `√(fraction)`.

Read against `Descent.Portability`, `family dimension coordinate` is one individual's
calibration error at population size `dimension`, `budget` counts the affected
subpopulation, and `rootMeanSquare` is the pooled quantity that
`ContinuumCalibration.calibrationDriftDefectSq` and the second moments behind
`PortabilityMasterTheorem.calibrationSlope` report. The corollary is stated abstractly
because this file sits below `Descent.Portability` in the layer order; the instantiation
belongs there, and needs only the support count and the amplitude ceiling. -/
theorem worstCase_survives_while_meanSquare_vanishes
    (family : ∀ dimension : ℕ, Fin dimension → ℝ) (budget : ℕ → ℕ)
    (hsupport : ∀ dimension : ℕ, ∃ support : Finset (Fin dimension),
      support.card ≤ budget dimension ∧
        ∀ coordinate ∉ support, family dimension coordinate = 0)
    (hbounded : ∀ dimension coordinate, |family dimension coordinate| ≤ 1)
    (hsevere : ∀ᶠ dimension in atTop, ∃ coordinate, |family dimension coordinate| = 1)
    (hvanishing : Tendsto (fun dimension : ℕ ↦ (budget dimension : ℝ) / (dimension : ℝ))
      atTop (𝓝 0)) :
    WorstCaseVisible family ∧
      Tendsto (fun dimension : ℕ ↦ rootMeanSquare (family dimension)) atTop (𝓝 0) := by
  constructor
  · refine ⟨1, zero_lt_one, ?_⟩
    filter_upwards [hsevere] with dimension hdimension
    obtain ⟨coordinate, hcoordinate⟩ := hdimension
    calc (1 : ℝ) = |family dimension coordinate| := hcoordinate.symm
      _ ≤ supremumNorm (family dimension) := le_supremumNorm _ _
  · exact tendsto_rootMeanSquare_of_supportFraction_tendsto_zero family budget 1
      hsupport hbounded hvanishing

end NormVisibility
end Descent.Blindness
