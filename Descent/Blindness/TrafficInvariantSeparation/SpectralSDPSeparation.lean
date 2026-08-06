/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Blindness.TrafficInvariantSeparation.InvariantSeparation

assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent.Blindness
namespace TrafficInvariantSeparation

open scoped Matrix Topology

/-!
# `TrafficInvariantSeparation.SpectralSDPSeparation`

Part of the split of `Descent/Blindness/TrafficInvariantSeparation.lean`, which was 6,618 lines.

The parts are a FAN: each imports the parts that declare the symbols it names, and nothing
else. The split first made them a CHAIN -- each importing the one before, in the order the
original text ran -- which preserved every resolution the single file had and charged every
part a dependency on everything written above it, used or not. Recovering the real order is
the work that chain deferred: each part's identifiers were resolved against its siblings'
declarations, and the imports above are the answer, so what a part rests on is readable
from its header instead of inherited from its position in a file that no longer exists.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/


section SpectralSDPSeparation

/-- One distinguished outlier coordinate together with `population` bulk
coordinates. -/
abbrev FiniteOutlierCoordinate (population : ℕ) := Option (Fin population)

/-- The baseline diagonal spectrum is constant. -/
def finiteBulkDiagonal (baseline : ℝ) (population : ℕ) :
    FiniteOutlierCoordinate population → ℝ :=
  fun _coordinate ↦ baseline

/-- A single positive spectral outlier, of normalized mass `1/(p+1)`. -/
def finiteOutlierDiagonal (baseline spikeStrength : ℝ) (population : ℕ) :
    FiniteOutlierCoordinate population → ℝ
  | none => baseline + spikeStrength
  | some _coordinate => baseline

/-- Normalized spectral moment of a finite diagonal design. -/
noncomputable def normalizedDiagonalSpectralMoment
    (population edges : ℕ)
    (diagonal : FiniteOutlierCoordinate population → ℝ) : ℝ :=
  (∑ coordinate, diagonal coordinate ^ edges) / (population + 1 : ℕ)

/-- Normalized empirical spectral average of an arbitrary fixed test
function. -/
noncomputable def normalizedDiagonalSpectralObservable
    (population : ℕ) (observable : ℝ → ℝ)
    (diagonal : FiniteOutlierCoordinate population → ℝ) : ℝ :=
  (∑ coordinate, observable (diagonal coordinate)) / (population + 1 : ℕ)

/-- The finite witness has exactly `p+1` spectral coordinates. -/
theorem finiteOutlierCoordinate_card (population : ℕ) :
    Fintype.card (FiniteOutlierCoordinate population) = population + 1 := by
  simp [FiniteOutlierCoordinate]

/-- The exact normalized-moment correction caused by the single outlier. -/
theorem normalizedDiagonalSpectralMoment_outlier_sub_bulk
    (baseline spikeStrength : ℝ) (population edges : ℕ) :
    normalizedDiagonalSpectralMoment population edges
        (finiteOutlierDiagonal baseline spikeStrength population) -
      normalizedDiagonalSpectralMoment population edges
        (finiteBulkDiagonal baseline population) =
      ((baseline + spikeStrength) ^ edges - baseline ^ edges) /
        (population + 1 : ℕ) := by
  simp [normalizedDiagonalSpectralMoment, finiteOutlierDiagonal,
    finiteBulkDiagonal]
  field_simp
  ring

/-- Every fixed normalized spectral moment misses the bounded rank-one
outlier asymptotically. -/
theorem normalizedDiagonalSpectralMoment_outlier_sub_bulk_tendsto_zero
    (baseline spikeStrength : ℝ) (edges : ℕ) :
    Filter.Tendsto
      (fun population ↦
        normalizedDiagonalSpectralMoment population edges
            (finiteOutlierDiagonal baseline spikeStrength population) -
          normalizedDiagonalSpectralMoment population edges
            (finiteBulkDiagonal baseline population))
      Filter.atTop (nhds 0) := by
  simpa only [normalizedDiagonalSpectralMoment_outlier_sub_bulk, Function.comp_def] using
    (tendsto_const_div_atTop_nhds_zero_nat
        ((baseline + spikeStrength) ^ edges - baseline ^ edges)).comp
      (Filter.tendsto_add_atTop_nat 1)

/-- The exact empirical-average correction for any fixed spectral test
function. -/
theorem normalizedDiagonalSpectralObservable_outlier_sub_bulk
    (baseline spikeStrength : ℝ) (population : ℕ) (observable : ℝ → ℝ) :
    normalizedDiagonalSpectralObservable population observable
        (finiteOutlierDiagonal baseline spikeStrength population) -
      normalizedDiagonalSpectralObservable population observable
        (finiteBulkDiagonal baseline population) =
      (observable (baseline + spikeStrength) - observable baseline) /
        (population + 1 : ℕ) := by
  simp [normalizedDiagonalSpectralObservable, finiteOutlierDiagonal,
    finiteBulkDiagonal]
  field_simp
  ring

/-- The single outlier is invisible to every fixed empirical spectral
observable, which directly expresses equality of the limiting bulk spectral
law rather than only equality of its moments. -/
theorem normalizedDiagonalSpectralObservable_outlier_sub_bulk_tendsto_zero
    (baseline spikeStrength : ℝ) (observable : ℝ → ℝ) :
    Filter.Tendsto
      (fun population ↦
        normalizedDiagonalSpectralObservable population observable
            (finiteOutlierDiagonal baseline spikeStrength population) -
          normalizedDiagonalSpectralObservable population observable
            (finiteBulkDiagonal baseline population))
      Filter.atTop (nhds 0) := by
  simpa only [normalizedDiagonalSpectralObservable_outlier_sub_bulk, Function.comp_def] using
    (tendsto_const_div_atTop_nhds_zero_nat
        (observable (baseline + spikeStrength) - observable baseline)).comp
      (Filter.tendsto_add_atTop_nat 1)

/-- A value is the maximum of a finite diagonal spectrum when it upper-bounds
every coordinate and is attained. -/
def IsDiagonalMaximum {Coordinate : Type*}
    (diagonal : Coordinate → ℝ) (maximum : ℝ) : Prop :=
  (∀ coordinate, diagonal coordinate ≤ maximum) ∧
    ∃ coordinate, diagonal coordinate = maximum

/-- The constant bulk spectrum has maximum equal to its baseline. -/
theorem finiteBulkDiagonal_hasMaximum (baseline : ℝ) (population : ℕ) :
    IsDiagonalMaximum (finiteBulkDiagonal baseline population) baseline := by
  exact ⟨fun _coordinate ↦ le_rfl,
    ⟨none, rfl⟩⟩

/-- A nonnegative outlier raises the exact spectral maximum by its full
strength, independently of its vanishing normalized mass. -/
theorem finiteOutlierDiagonal_hasMaximum
    (baseline spikeStrength : ℝ) (population : ℕ) (hspike : 0 ≤ spikeStrength) :
    IsDiagonalMaximum
      (finiteOutlierDiagonal baseline spikeStrength population)
      (baseline + spikeStrength) := by
  constructor
  · intro coordinate
    cases coordinate with
    | none => exact le_rfl
    | some coordinate =>
        simp only [finiteOutlierDiagonal]
        linarith
  · exact ⟨none, rfl⟩

/-- Feasible points of the trace-one positive-semidefinite matrix program. -/
def IsTraceOnePSDMatrix {Coordinate : Type*} [Fintype Coordinate]
    (matrix : Matrix Coordinate Coordinate ℝ) : Prop :=
  matrix.PosSemidef ∧ Matrix.trace matrix = 1

/-- Objective of the trace-one SDP with diagonal design spectrum. -/
noncomputable def diagonalTraceOneSDPObjective
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (diagonal : Coordinate → ℝ) (matrix : Matrix Coordinate Coordinate ℝ) : ℝ :=
  Matrix.trace (Matrix.diagonal diagonal * matrix)

/-- A number is the SDP optimum when it upper-bounds every feasible value and
is attained by one feasible matrix. -/
def IsDiagonalTraceOneSDPOptimum
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (diagonal : Coordinate → ℝ) (optimum : ℝ) : Prop :=
  (∀ matrix, IsTraceOnePSDMatrix matrix →
    diagonalTraceOneSDPObjective diagonal matrix ≤ optimum) ∧
  ∃ matrix, IsTraceOnePSDMatrix matrix ∧
    diagonalTraceOneSDPObjective diagonal matrix = optimum

/-- Every diagonal entry of a real positive-semidefinite matrix is
nonnegative. -/
theorem posSemidef_diagonalEntry_nonnegative
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {matrix : Matrix Coordinate Coordinate ℝ} (hmatrix : matrix.PosSemidef)
    (coordinate : Coordinate) :
    0 ≤ matrix coordinate coordinate := by
  simpa using hmatrix.2 (Pi.single coordinate 1)

/-- The diagonal SDP objective is the diagonal weighted sum. -/
theorem diagonalTraceOneSDPObjective_eq_sum
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (diagonal : Coordinate → ℝ) (matrix : Matrix Coordinate Coordinate ℝ) :
    diagonalTraceOneSDPObjective diagonal matrix =
      ∑ coordinate, diagonal coordinate * matrix coordinate coordinate := by
  unfold diagonalTraceOneSDPObjective
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]

/-- **Exact trace-one SDP solution for a diagonal objective.**  The optimum is
the largest diagonal entry.  The upper bound uses PSD diagonal
nonnegativity and trace one; a rank-one diagonal projector attains it. -/
theorem diagonalTraceOneSDPOptimum_of_isDiagonalMaximum
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (diagonal : Coordinate → ℝ) (maximum : ℝ)
    (hmaximum : IsDiagonalMaximum diagonal maximum) :
    IsDiagonalTraceOneSDPOptimum diagonal maximum := by
  constructor
  · intro matrix hfeasible
    rw [diagonalTraceOneSDPObjective_eq_sum]
    calc
      (∑ coordinate, diagonal coordinate * matrix coordinate coordinate) ≤
          ∑ coordinate, maximum * matrix coordinate coordinate := by
        apply Finset.sum_le_sum
        intro coordinate _hcoordinate
        exact mul_le_mul_of_nonneg_right (hmaximum.1 coordinate)
          (posSemidef_diagonalEntry_nonnegative hfeasible.1 coordinate)
      _ = maximum * Matrix.trace matrix := by
        rw [Matrix.trace, Finset.mul_sum]
        rfl
      _ = maximum := by rw [hfeasible.2, mul_one]
  · obtain ⟨coordinate, hcoordinate⟩ := hmaximum.2
    let witness : Matrix Coordinate Coordinate ℝ :=
      Matrix.diagonal (Pi.single coordinate 1)
    refine ⟨witness, ?_, ?_⟩
    · constructor
      · apply Matrix.PosSemidef.diagonal
        intro index
        by_cases hindex : index = coordinate <;> simp [Pi.single_apply, hindex]
      · simp [witness, Matrix.trace]
    · simp [witness, diagonalTraceOneSDPObjective_eq_sum, Pi.single_apply,
        hcoordinate]

/-- The full finite/infinite separation contract for a bulk-invisible spectral
outlier and the trace-one SDP it changes. -/
def BulkSpectralLawExtremalSDPSeparation
    (baseline spikeStrength : ℝ) : Prop :=
    (∀ observable : ℝ → ℝ,
      Filter.Tendsto
        (fun population ↦
          normalizedDiagonalSpectralObservable population observable
              (finiteOutlierDiagonal baseline spikeStrength population) -
            normalizedDiagonalSpectralObservable population observable
              (finiteBulkDiagonal baseline population))
        Filter.atTop (nhds 0)) ∧
    ∀ population : ℕ,
      IsDiagonalMaximum (finiteBulkDiagonal baseline population) baseline ∧
      IsDiagonalMaximum (finiteOutlierDiagonal baseline spikeStrength population)
        (baseline + spikeStrength) ∧
      IsDiagonalTraceOneSDPOptimum (finiteBulkDiagonal baseline population) baseline ∧
      IsDiagonalTraceOneSDPOptimum
        (finiteOutlierDiagonal baseline spikeStrength population)
        (baseline + spikeStrength) ∧
      baseline < baseline + spikeStrength

/-- **Bulk spectral law does not determine extremal spectral or SDP data.**
The baseline and one-outlier sequences have asymptotically identical averages
for every fixed spectral test function.  Nevertheless, at every finite size,
their spectral maxima and trace-one PSD SDP optima differ by exactly the
positive spike strength. -/
theorem bulkSpectralLaw_invisible_extremalSpectrumAndSDP_visible
    (baseline spikeStrength : ℝ) (hspike : 0 < spikeStrength) :
    BulkSpectralLawExtremalSDPSeparation baseline spikeStrength := by
  rw [BulkSpectralLawExtremalSDPSeparation]
  refine ⟨normalizedDiagonalSpectralObservable_outlier_sub_bulk_tendsto_zero
      baseline spikeStrength, ?_⟩
  intro population
  have hbulk := finiteBulkDiagonal_hasMaximum baseline population
  have houtlier := finiteOutlierDiagonal_hasMaximum baseline spikeStrength population
    hspike.le
  exact ⟨hbulk, houtlier,
    diagonalTraceOneSDPOptimum_of_isDiagonalMaximum _ _ hbulk,
    diagonalTraceOneSDPOptimum_of_isDiagonalMaximum _ _ houtlier, by linarith⟩

end SpectralSDPSeparation

end TrafficInvariantSeparation
end Descent.Blindness
