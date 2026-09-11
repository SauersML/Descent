/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.UniversalMetricIdentification
import Mathlib.Analysis.Convex.Combination

assert_below Descent.Decision Descent.Program

/-!
# The sharp region a partially accumulated report vector can still reach

A computation that has accumulated part of a report vector and left some cells unresolved
cannot name the final vector, but it can name exactly the set of vectors that remain
possible. NOTE 2 section 8 identifies that set: the accumulated vector shifted by the
mass-weighted Minkowski sum of the convex hulls of the per-cell value sets.

`completionRegion` is NOTE 2 equation (33). Two statements pin it down. `completionMean_mem`
shows that the mean of any actual completion, a finite report law on each cell supported in
that cell's value set, lies in the region, and `completion_coordinate` identifies the
coordinates of that mean with the corpus expectation of the coordinate statistic.
`mem_convexHull_attained` is the converse at the level of one cell: any point of the convex
hull of a value set is the mean of a finite report law supported in that set, so no point of
the region is spurious. The two together say the region is the exact range of completions.
Assembling the per-cell laws into one indexed family over all cells would require a common
outcome type and is not carried out here; nothing in the region statement depends on it.

`support_isGreatest` is NOTE 2 equation (34). Given, for each cell, a value that is greatest
among the direction's values on that cell's value set, the direction's greatest value over
the whole region is the direction at the accumulated vector plus the mass-weighted sum of
those per-cell greatest values. The proof does not use compactness: the per-cell maxima are
taken as data, which is what a certificate holds anyway, and the two halves are that a
half-space containing a value set contains its convex hull, and that placing each cell at its
own maximizer attains the bound. `support_csSup` restates it as the supremum.

Scope: the cells and the coordinates are finite types and the value sets are arbitrary sets
of coordinate vectors, with no topology assumed. Compactness enters only if one wants the
per-cell maxima to exist rather than to be given; that existence is not proved here. Nothing
here says which completions a demographic history actually permits.

## Empirical status

None. The bodies here are convex geometry: a Minkowski sum of convex hulls and the value of a
linear functional on it, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FrontierCompletionRegion

variable {Cell Coord : Type*} [Fintype Cell] [Fintype Coord]

/-- **NOTE 2 equation (33).** The report vectors an accumulated frontier can still reach: the
accumulated vector shifted by the mass-weighted Minkowski sum of the convex hulls of the
per-cell value sets. -/
def completionRegion (baseline : Coord → ℝ) (cellMass : Cell → ℝ)
    (values : Cell → Set (Coord → ℝ)) : Set (Coord → ℝ) :=
  {vector | ∃ choice : Cell → Coord → ℝ,
    (∀ cell, choice cell ∈ convexHull ℝ (values cell)) ∧
      vector = baseline + ∑ cell, cellMass cell • choice cell}

/-- The mean of a finite report law supported in a value set lies in that set's convex
hull. -/
theorem mean_mem_convexHull {Outcome : Type*} [Fintype Outcome] (valueSet : Set (Coord → ℝ))
    (law : FiniteReportLaw Outcome) (value : Outcome → Coord → ℝ)
    (hvalue : ∀ outcome, value outcome ∈ valueSet) :
    (∑ outcome, law.mass outcome • value outcome) ∈ convexHull ℝ valueSet :=
  (convex_convexHull ℝ valueSet).sum_mem (fun outcome _ ↦ law.mass_nonneg outcome) law.mass_sum
    fun outcome _ ↦ subset_convexHull ℝ valueSet (hvalue outcome)

/-- Every point of the convex hull of a value set is the mean of a finite report law supported
in that set, so the hull adds no point that no completion realizes. -/
theorem mem_convexHull_attained (valueSet : Set (Coord → ℝ)) (point : Coord → ℝ)
    (hpoint : point ∈ convexHull ℝ valueSet) :
    ∃ (Outcome : Type) (_ : Fintype Outcome) (law : FiniteReportLaw Outcome)
      (value : Outcome → Coord → ℝ), (∀ outcome, value outcome ∈ valueSet) ∧
        point = ∑ outcome, law.mass outcome • value outcome := by
  obtain ⟨Outcome, outcomeFintype, weight, value, hweight, hsum, hvalue, hcombination⟩ :=
    mem_convexHull_iff_exists_fintype.mp hpoint
  exact ⟨Outcome, outcomeFintype, ⟨weight, hweight, hsum⟩, value, hvalue, hcombination.symm⟩

/-- **NOTE 2 equation (33), soundness.** The mean of any completion, a finite report law on
each cell supported in that cell's value set, lies in the completion region. -/
theorem completionMean_mem (baseline : Coord → ℝ) (cellMass : Cell → ℝ)
    (values : Cell → Set (Coord → ℝ)) {Outcome : Type*} [Fintype Outcome]
    (law : Cell → FiniteReportLaw Outcome) (value : Cell → Outcome → Coord → ℝ)
    (hvalue : ∀ cell outcome, value cell outcome ∈ values cell) :
    baseline + ∑ cell, cellMass cell •
        ∑ outcome, (law cell).mass outcome • value cell outcome ∈
      completionRegion baseline cellMass values :=
  ⟨fun cell ↦ ∑ outcome, (law cell).mass outcome • value cell outcome,
    fun cell ↦ mean_mem_convexHull (values cell) (law cell) (value cell) (hvalue cell), rfl⟩

/-- Each coordinate of a cell mean is the corpus expectation of that coordinate statistic. -/
theorem completion_coordinate {Outcome : Type*} [Fintype Outcome]
    (law : FiniteReportLaw Outcome) (value : Outcome → Coord → ℝ) (coord : Coord) :
    (∑ outcome, law.mass outcome • value outcome) coord =
      law.expectation (fun outcome ↦ value outcome coord) := by
  simp [FiniteReportLaw.expectation, Finset.sum_apply]

/-- The value a direction assigns to a report vector. -/
noncomputable def directionValue (direction vector : Coord → ℝ) : ℝ :=
  ∑ coord, direction coord * vector coord

/-- A direction's sublevel set is convex, which is what lets a bound on a value set pass to
its convex hull. -/
theorem convex_directionValue_le (direction : Coord → ℝ) (bound : ℝ) :
    Convex ℝ {vector : Coord → ℝ | directionValue direction vector ≤ bound} := by
  intro first hfirst second hsecond weightFirst weightSecond hfirstNonneg hsecondNonneg hone
  simp only [Set.mem_setOf_eq, directionValue] at hfirst hsecond ⊢
  have hcombination : ∑ coord, direction coord *
      (weightFirst • first + weightSecond • second) coord =
        weightFirst * (∑ coord, direction coord * first coord) +
          weightSecond * ∑ coord, direction coord * second coord := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun coord _ ↦ by ring
  have hsplit : weightFirst * bound + weightSecond * bound = bound := by
    rw [← add_mul, hone, one_mul]
  rw [hcombination]
  linarith [mul_le_mul_of_nonneg_left hfirst hfirstNonneg,
    mul_le_mul_of_nonneg_left hsecond hsecondNonneg]

/-- A direction evaluates a completion by evaluating the accumulated vector and then the
per-cell choices, weighted by the cell masses. -/
theorem directionValue_completion (direction baseline : Coord → ℝ) (cellMass : Cell → ℝ)
    (choice : Cell → Coord → ℝ) :
    directionValue direction (baseline + ∑ cell, cellMass cell • choice cell) =
      directionValue direction baseline +
        ∑ cell, cellMass cell * directionValue direction (choice cell) := by
  have hpoint : ∀ coord : Coord,
      direction coord * (baseline + ∑ cell, cellMass cell • choice cell) coord =
        direction coord * baseline coord +
          ∑ cell, cellMass cell * (direction coord * choice cell coord) := by
    intro coord
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun cell _ ↦ by ring
  unfold directionValue
  rw [Finset.sum_congr rfl fun coord _ ↦ hpoint coord, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun cell _ ↦ (Finset.mul_sum _ _ _).symm

/-- **NOTE 2 equation (34).** The greatest value a direction takes on the completion region is
its value at the accumulated vector plus the mass-weighted sum of the greatest values it takes
on the per-cell value sets. The lower half places every cell at its own maximizer; the upper
half is that the half-space cutting a value set at its maximum also contains that set's convex
hull.

Assumes: `cellMax cell` is greatest among the direction's values on `values cell`, which is
the per-cell certificate a frontier computation already holds. -/
theorem support_isGreatest (direction baseline : Coord → ℝ) (cellMass : Cell → ℝ)
    (hmass : ∀ cell, 0 ≤ cellMass cell) (values : Cell → Set (Coord → ℝ))
    (cellMax : Cell → ℝ)
    (hcellMax : ∀ cell,
      IsGreatest {value | ∃ point ∈ values cell, directionValue direction point = value}
        (cellMax cell)) :
    IsGreatest {value | ∃ vector ∈ completionRegion baseline cellMass values,
        directionValue direction vector = value}
      (directionValue direction baseline + ∑ cell, cellMass cell * cellMax cell) := by
  constructor
  · choose extreme hextreme hattains using fun cell ↦ (hcellMax cell).1
    refine ⟨baseline + ∑ cell, cellMass cell • extreme cell,
      ⟨extreme, fun cell ↦ subset_convexHull ℝ (values cell) (hextreme cell), rfl⟩, ?_⟩
    rw [directionValue_completion]
    congr 1
    exact Finset.sum_congr rfl fun cell _ ↦ by rw [hattains cell]
  · rintro value ⟨vector, hvector, rfl⟩
    obtain ⟨choice, hchoice, hshape⟩ := hvector
    subst hshape
    rw [directionValue_completion]
    have hcell : ∀ cell, directionValue direction (choice cell) ≤ cellMax cell := by
      intro cell
      have hsubset : values cell ⊆
          {point : Coord → ℝ | directionValue direction point ≤ cellMax cell} :=
        fun point hpoint ↦ (hcellMax cell).2 ⟨point, hpoint, rfl⟩
      exact convexHull_min hsubset (convex_directionValue_le direction (cellMax cell))
        (hchoice cell)
    have hweighted : ∑ cell, cellMass cell * directionValue direction (choice cell) ≤
        ∑ cell, cellMass cell * cellMax cell :=
      Finset.sum_le_sum fun cell _ ↦ mul_le_mul_of_nonneg_left (hcell cell) (hmass cell)
    linarith

/-- **NOTE 2 equation (34), supremum form.** The support function of the completion region is
the support value of the accumulated vector plus the mass-weighted sum of the per-cell support
values.

Assumes: `cellMax cell` is greatest among the direction's values on `values cell`. -/
theorem support_csSup (direction baseline : Coord → ℝ) (cellMass : Cell → ℝ)
    (hmass : ∀ cell, 0 ≤ cellMass cell) (values : Cell → Set (Coord → ℝ))
    (cellMax : Cell → ℝ)
    (hcellMax : ∀ cell,
      IsGreatest {value | ∃ point ∈ values cell, directionValue direction point = value}
        (cellMax cell)) :
    sSup {value | ∃ vector ∈ completionRegion baseline cellMass values,
        directionValue direction vector = value} =
      directionValue direction baseline + ∑ cell, cellMass cell * cellMax cell :=
  (support_isGreatest direction baseline cellMass hmass values cellMax hcellMax).csSup_eq

end Descent.Portability.FrontierCompletionRegion
