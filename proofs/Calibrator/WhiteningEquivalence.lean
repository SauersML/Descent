import Mathlib.LinearAlgebra.Matrix.DotProduct

namespace Calibrator

open scoped Matrix

/-!
# Exact right-whitening equivalence

The results here are deterministic matrix identities.  They justify treating
right-whitening as an equivalence of statistical experiments whenever the
coloring matrix is invertible; no distributional assumption on the noise is
used.
-/

variable {rows cols : Type*}
  [Fintype cols] [DecidableEq cols]

/-- Right-whiten every row of a rectangular data matrix. -/
def rightWhiten (inverseColor : Matrix cols cols ℝ)
    (data : Matrix rows cols ℝ) : Matrix rows cols ℝ :=
  Matrix.mul data inverseColor

/-- Restore the original right-side coloring. -/
def rightColor (color : Matrix cols cols ℝ)
    (data : Matrix rows cols ℝ) : Matrix rows cols ℝ :=
  Matrix.mul data color

/-- Coloring followed by whitening removes the correlated-noise factor
exactly and transports the signal by the same invertible coordinate change. -/
theorem right_whitening_removes_coloring
    (signal noise : Matrix rows cols ℝ)
    (color inverseColor : Matrix cols cols ℝ)
    (hrightInverse : Matrix.mul color inverseColor = 1) :
    rightWhiten inverseColor (signal + Matrix.mul noise color) =
      rightWhiten inverseColor signal + noise := by
  unfold rightWhiten
  rw [Matrix.add_mul, Matrix.mul_assoc, hrightInverse, Matrix.mul_one]

/-- Whitening and recoloring are inverse operations in one direction. -/
theorem rightColor_leftInverse_rightWhiten
    (color inverseColor : Matrix cols cols ℝ)
    (hleftInverse : Matrix.mul inverseColor color = 1) :
    Function.LeftInverse (rightColor color : Matrix rows cols ℝ → Matrix rows cols ℝ)
      (rightWhiten inverseColor) := by
  intro data
  unfold rightColor rightWhiten
  rw [Matrix.mul_assoc, hleftInverse, Matrix.mul_one]

/-- Whitening and recoloring are inverse operations in the other direction. -/
theorem rightColor_rightInverse_rightWhiten
    (color inverseColor : Matrix cols cols ℝ)
    (hrightInverse : Matrix.mul color inverseColor = 1) :
    Function.RightInverse (rightColor color : Matrix rows cols ℝ → Matrix rows cols ℝ)
      (rightWhiten inverseColor) := by
  intro data
  unfold rightColor rightWhiten
  rw [Matrix.mul_assoc, hrightInverse, Matrix.mul_one]

/-- An invertible right-whitening map is a measurable-model-independent
bijection of data spaces, with recoloring as its explicit inverse. -/
theorem rightWhiten_bijective
    (color inverseColor : Matrix cols cols ℝ)
    (hleftInverse : Matrix.mul inverseColor color = 1)
    (hrightInverse : Matrix.mul color inverseColor = 1) :
    Function.Bijective (rightWhiten inverseColor :
      Matrix rows cols ℝ → Matrix rows cols ℝ) := by
  have hleft := rightColor_leftInverse_rightWhiten
    (rows := rows) color inverseColor hleftInverse
  have hright := rightColor_rightInverse_rightWhiten
    (rows := rows) color inverseColor hrightInverse
  exact ⟨hleft.injective, hright.surjective⟩

end Calibrator
