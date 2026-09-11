/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactFiniteHistoryLaw
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Compact

assert_below Descent.Decision Descent.Program

/-!
# The sharp region a partially accumulated report vector can still reach

A computation that has accumulated part of a report vector and left some cells unresolved
cannot name the final vector, but it can name exactly the set of vectors that remain
possible. NOTE 2 section 8 identifies that set: the accumulated vector shifted by the
mass-weighted Minkowski sum of the convex hulls of the per-cell value sets.

`completionRegion` is NOTE 2 equation (33). `completionMean_mem` shows that the mean of any
actual completion, a finite report law on each cell supported in that cell's value set, lies in
the region, and `completion_coordinate` identifies the coordinates of that mean with the corpus
expectation of the coordinate statistic. `mem_convexHull_attained` is the converse at the level
of one cell: any point of the convex hull of a value set is the mean of a finite report law
supported in that set. `completionRegion_attained` assembles those per-cell laws into one
completion on a common outcome type, the disjoint union of the per-cell outcome types, as in
the weighted union of NOTE 2's proof: each cell's law is pushed forward along that cell's
inclusion with the corpus `FiniteReportLaw.pushforward`, and an outcome belonging to another
cell, which carries no mass, reports a fixed point of the cell's own value set
(`sigmaCellValue`, `sigmaCellMean`). `mem_completionRegion_iff` states both directions at once:
the region is exactly the set of completion means.

`support_isGreatest` is NOTE 2 equation (34). Given, for each cell, a value that is greatest
among the direction's values on that cell's value set, the direction's greatest value over
the whole region is the direction at the accumulated vector plus the mass-weighted sum of
those per-cell greatest values. The two halves are that a half-space containing a value set
contains its convex hull, and that placing each cell at its own maximizer attains the bound.
`support_csSup` restates it as the supremum. For the compact value sets NOTE 2 assumes, the
per-cell maxima exist: a direction is continuous (`continuous_directionValue`), so it attains
its maximum on a nonempty compact set (`exists_cellMaximizer`), and `cellSupport`, the supremum
of its values there, is that maximum (`cellSupport_isGreatest`).
`support_isGreatest_of_isCompact` and `support_csSup_of_isCompact` are (34) with the displayed
maxima and no per-cell certificate supplied.

Scope: the cells and the coordinates are finite types. The region statements take arbitrary
sets of coordinate vectors with no topology; compactness and nonemptiness are hypotheses only
of the compact forms of (34). The conditional-mean image map of the same section is
`conditionalMeans`, and `exists_convex_not_convex_conditionalMeans` makes precise the note's
remark that its image of a convex set of completions need not be convex, so that coordinate
intervals lose the coupling between metrics. The certificate (35) is not treated here. Nothing
here says which completions a demographic history actually permits.

## Empirical status

None. The bodies here are convex geometry: a Minkowski sum of convex hulls and the value of a
linear functional on it, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace Descent.Portability.FrontierCompletionRegion

variable {Cell : Type u} {Coord : Type v} [Fintype Cell] [Fintype Coord]

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

/-! ## One completion on a common outcome type -/

/-- The value one cell's completion reports on the disjoint union of all cells' outcomes: the
cell's own report value on its own outcomes, and a fixed point `anchor cell` of the cell's
value set on every other cell's outcomes, which that cell's completion never visits. -/
def sigmaCellValue [DecidableEq Cell] {Outcome : Cell → Type*}
    (value : ∀ cell, Outcome cell → Coord → ℝ) (anchor : Cell → Coord → ℝ) (cell : Cell)
    (outcome : Σ other, Outcome other) : Coord → ℝ :=
  if outcome.1 = cell then value outcome.1 outcome.2 else anchor cell

/-- A spread value lies in its cell's value set when the cell's own values and its anchor
do. -/
theorem sigmaCellValue_mem [DecidableEq Cell] {Outcome : Cell → Type*}
    (values : Cell → Set (Coord → ℝ)) (value : ∀ cell, Outcome cell → Coord → ℝ)
    (anchor : Cell → Coord → ℝ) (hvalue : ∀ cell outcome, value cell outcome ∈ values cell)
    (hanchor : ∀ cell, anchor cell ∈ values cell) (cell : Cell)
    (outcome : Σ other, Outcome other) :
    sigmaCellValue value anchor cell outcome ∈ values cell := by
  obtain ⟨other, own⟩ := outcome
  by_cases hother : other = cell
  · subst hother
    simpa [sigmaCellValue] using hvalue other own
  · simpa [sigmaCellValue, hother] using hanchor cell

/-- Pushing a cell's completion law forward along that cell's inclusion into the disjoint
union of outcomes, and reading the spread values there, reproduces the cell's own mean. -/
theorem sigmaCellMean [DecidableEq Cell] {Outcome : Cell → Type*}
    [∀ cell, Fintype (Outcome cell)] (law : ∀ cell, FiniteReportLaw (Outcome cell))
    (value : ∀ cell, Outcome cell → Coord → ℝ) (anchor : Cell → Coord → ℝ) (cell : Cell) :
    ∑ outcome, ((law cell).pushforward (Sigma.mk cell)).mass outcome •
        sigmaCellValue value anchor cell outcome =
      ∑ outcome, (law cell).mass outcome • value cell outcome := by
  funext coord
  rw [completion_coordinate, completion_coordinate, FiniteReportLaw.expectation_pushforward]
  simp [sigmaCellValue]

/-- **NOTE 2 equation (33), global attainment.** Every vector of the completion region is the
mean of ONE completion on a common outcome type: the disjoint union of per-cell outcome types,
carrying on each cell the pushforward of a law that realizes that cell's convex combination. -/
theorem completionRegion_attained (baseline : Coord → ℝ) (cellMass : Cell → ℝ)
    (values : Cell → Set (Coord → ℝ)) (vector : Coord → ℝ)
    (hvector : vector ∈ completionRegion baseline cellMass values) :
    ∃ (Outcome : Type u) (_ : Fintype Outcome) (law : Cell → FiniteReportLaw Outcome)
      (value : Cell → Outcome → Coord → ℝ), (∀ cell outcome, value cell outcome ∈ values cell) ∧
        vector = baseline + ∑ cell, cellMass cell •
          ∑ outcome, (law cell).mass outcome • value cell outcome := by
  classical
  obtain ⟨choice, hchoice, rfl⟩ := hvector
  choose Outcome outcomeFintype law value hvalue hmean using
    fun cell ↦ mem_convexHull_attained (values cell) (choice cell) (hchoice cell)
  have hnonempty : ∀ cell, (values cell).Nonempty :=
    fun cell ↦ convexHull_nonempty_iff.mp ⟨choice cell, hchoice cell⟩
  refine ⟨(Σ cell, Outcome cell), inferInstance,
    (fun cell ↦ (law cell).pushforward (Sigma.mk cell)),
    (sigmaCellValue value fun cell ↦ (hnonempty cell).some),
    (sigmaCellValue_mem values value _ hvalue fun cell ↦ (hnonempty cell).some_mem), ?_⟩
  congr 1
  refine Finset.sum_congr rfl fun cell _ ↦ ?_
  rw [sigmaCellMean, ← hmean cell]

/-- **NOTE 2 equation (33), the region is the range of completions.** A vector lies in the
completion region exactly when it is the mean of a completion on a common outcome type. -/
theorem mem_completionRegion_iff (baseline : Coord → ℝ) (cellMass : Cell → ℝ)
    (values : Cell → Set (Coord → ℝ)) (vector : Coord → ℝ) :
    vector ∈ completionRegion baseline cellMass values ↔
      ∃ (Outcome : Type u) (_ : Fintype Outcome) (law : Cell → FiniteReportLaw Outcome)
        (value : Cell → Outcome → Coord → ℝ),
          (∀ cell outcome, value cell outcome ∈ values cell) ∧
            vector = baseline + ∑ cell, cellMass cell •
              ∑ outcome, (law cell).mass outcome • value cell outcome := by
  refine ⟨completionRegion_attained baseline cellMass values vector, ?_⟩
  rintro ⟨Outcome, outcomeFintype, law, value, hvalue, rfl⟩
  exact completionMean_mem baseline cellMass values law value hvalue

/-! ## The support function -/

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

/-! ## Compact value sets: the per-cell maxima exist -/

/-- A direction's value is a continuous function of the report vector. -/
theorem continuous_directionValue (direction : Coord → ℝ) :
    Continuous (directionValue direction) := by
  show Continuous fun vector : Coord → ℝ ↦ ∑ coord, direction coord * vector coord
  exact continuous_finset_sum Finset.univ fun coord _ ↦
    continuous_const.mul (continuous_apply coord)

/-- The support value of a value set in a direction: the least upper bound of the values the
direction takes on the set. -/
noncomputable def cellSupport (direction : Coord → ℝ) (valueSet : Set (Coord → ℝ)) : ℝ :=
  sSup {value | ∃ point ∈ valueSet, directionValue direction point = value}

/-- On a nonempty compact value set a direction attains its maximum at a point of the set. -/
theorem exists_cellMaximizer (direction : Coord → ℝ) (valueSet : Set (Coord → ℝ))
    (hcompact : IsCompact valueSet) (hnonempty : valueSet.Nonempty) :
    ∃ point ∈ valueSet, IsMaxOn (directionValue direction) valueSet point :=
  hcompact.exists_isMaxOn hnonempty (continuous_directionValue direction).continuousOn

/-- **The displayed maxima of NOTE 2 (34) exist.** On a nonempty compact value set the support
value is the greatest value the direction takes there. -/
theorem cellSupport_isGreatest (direction : Coord → ℝ) (valueSet : Set (Coord → ℝ))
    (hcompact : IsCompact valueSet) (hnonempty : valueSet.Nonempty) :
    IsGreatest {value | ∃ point ∈ valueSet, directionValue direction point = value}
      (cellSupport direction valueSet) :=
  (hcompact.image (continuous_directionValue direction)).isGreatest_sSup
    (hnonempty.image (directionValue direction))

/-- **NOTE 2 equation (34) for compact value sets.** When every per-cell value set is nonempty
and compact, the greatest value a direction takes on the completion region is its value at the
accumulated vector plus the mass-weighted sum of the per-cell support values, each of them
attained. -/
theorem support_isGreatest_of_isCompact (direction baseline : Coord → ℝ) (cellMass : Cell → ℝ)
    (hmass : ∀ cell, 0 ≤ cellMass cell) (values : Cell → Set (Coord → ℝ))
    (hcompact : ∀ cell, IsCompact (values cell)) (hnonempty : ∀ cell, (values cell).Nonempty) :
    IsGreatest {value | ∃ vector ∈ completionRegion baseline cellMass values,
        directionValue direction vector = value}
      (directionValue direction baseline +
        ∑ cell, cellMass cell * cellSupport direction (values cell)) :=
  support_isGreatest direction baseline cellMass hmass values _
    fun cell ↦ cellSupport_isGreatest direction (values cell) (hcompact cell) (hnonempty cell)

/-- **NOTE 2 equation (34), support function for compact value sets.** The support function
of the completion region is the direction at the accumulated vector plus the mass-weighted sum
of the per-cell maxima. -/
theorem support_csSup_of_isCompact (direction baseline : Coord → ℝ) (cellMass : Cell → ℝ)
    (hmass : ∀ cell, 0 ≤ cellMass cell) (values : Cell → Set (Coord → ℝ))
    (hcompact : ∀ cell, IsCompact (values cell)) (hnonempty : ∀ cell, (values cell).Nonempty) :
    sSup {value | ∃ vector ∈ completionRegion baseline cellMass values,
        directionValue direction vector = value} =
      directionValue direction baseline +
        ∑ cell, cellMass cell * cellSupport direction (values cell) :=
  (support_isGreatest_of_isCompact direction baseline cellMass hmass values hcompact
    hnonempty).csSup_eq

/-! ## The conditional-mean image need not be convex -/

/-- The conditional means of a joint domain/numerator report: each metric's numerator divided
by its defined mass, the map `(d_j, n_j)_j ↦ (n_j / d_j)_j` of NOTE 2 section 8. -/
noncomputable def conditionalMeans {Metric : Type*} (pairs : Metric → ℝ × ℝ) : Metric → ℝ :=
  fun metric ↦ (pairs metric).2 / (pairs metric).1

/-- **NOTE 2 section 8, the conditional-mean image need not be convex.** A convex set of joint
domain/numerator pairs, with every domain positive, whose image under the conditional-mean map
is not convex. Along one segment of completions two metrics reach the conditional means
`(1, 0)` and `(0, 1)` but never their midpoint, so independent coordinate intervals would
report a pair of conditional means that no completion attains. -/
theorem exists_convex_not_convex_conditionalMeans :
    ∃ pairs : Set (Fin 2 → ℝ × ℝ), Convex ℝ pairs ∧
      (∀ point ∈ pairs, ∀ metric, 0 < (point metric).1) ∧
        ¬ Convex ℝ (conditionalMeans '' pairs) := by
  let first : Fin 2 → ℝ × ℝ := ![(1, 1), (1, 0)]
  let second : Fin 2 → ℝ × ℝ := ![(1 / 2, 0), (1, 1)]
  have hcombination : ∀ weight : ℝ,
      (1 - weight) • first + weight • second = ![(1 - weight / 2, 1 - weight), (1, weight)] := by
    intro weight
    funext metric
    fin_cases metric <;> ext <;> simp [first, second] <;> ring
  refine ⟨segment ℝ first second, convex_segment first second, ?_, ?_⟩
  · rintro point ⟨a, b, ha, hb, hab, rfl⟩ metric
    obtain rfl : a = 1 - b := by linarith
    rw [hcombination]
    fin_cases metric <;> simp <;> linarith
  · intro hconvex
    have hfirst : conditionalMeans first ∈ conditionalMeans '' segment ℝ first second :=
      ⟨first, left_mem_segment ℝ first second, rfl⟩
    have hsecond : conditionalMeans second ∈ conditionalMeans '' segment ℝ first second :=
      ⟨second, right_mem_segment ℝ first second, rfl⟩
    obtain ⟨point, ⟨a, b, ha, hb, hab, rfl⟩, hpoint⟩ :=
      hconvex hfirst hsecond (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)
    obtain rfl : a = 1 - b := by linarith
    rw [hcombination] at hpoint
    have hsecondMetric := congrFun hpoint 1
    have hfirstMetric := congrFun hpoint 0
    simp [conditionalMeans, first, second] at hsecondMetric hfirstMetric
    rw [hsecondMetric] at hfirstMetric
    norm_num at hfirstMetric

end Descent.Portability.FrontierCompletionRegion
