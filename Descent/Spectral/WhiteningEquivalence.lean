/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Real.Basic

namespace Descent.Spectral

/-!
# Exact right-whitening equivalence

Right multiplication of a data matrix is represented rowwise: transforming a
row by `K` is `Kᵀ.mulVec`.  This formulation states the experiment equivalence
without relying on overloaded rectangular-matrix notation.
-/

variable {rows cols : Type*} [Fintype cols]

/-- Apply a right-side linear transformation independently to every data row. -/
def rightTransform (transform : Matrix cols cols ℝ)
    (data : Matrix rows cols ℝ) : Matrix rows cols ℝ :=
  fun row ↦ transform.transpose.mulVec (data row)

/-- Right-whitening is the row transformation induced by the inverse coloring
operator. -/
def rightWhiten (inverseColor : Matrix cols cols ℝ)
    (data : Matrix rows cols ℝ) : Matrix rows cols ℝ :=
  rightTransform inverseColor data

/-- Restore the original right-side coloring. -/
def rightColor (color : Matrix cols cols ℝ)
    (data : Matrix rows cols ℝ) : Matrix rows cols ℝ :=
  rightTransform color data

theorem rightTransform_add
    (transform : Matrix cols cols ℝ) (x y : Matrix rows cols ℝ) :
    rightTransform transform (x + y) =
      rightTransform transform x + rightTransform transform y := by
  ext row col
  simp [rightTransform, Matrix.mulVec, dotProduct, Finset.sum_add_distrib,
    mul_add]

/-- Coloring followed by whitening removes the noise coloring exactly and
transports the signal by the same invertible coordinate change. -/
theorem right_whitening_removes_coloring
    (signal noise : Matrix rows cols ℝ)
    (color inverseColor : Matrix cols cols ℝ)
    (hremove : Function.LeftInverse
      (fun x ↦ inverseColor.transpose.mulVec x)
      (fun x ↦ color.transpose.mulVec x)) :
    rightWhiten inverseColor (signal + rightColor color noise) =
      rightWhiten inverseColor signal + noise := by
  rw [rightWhiten, rightTransform_add]
  congr 1
  ext row col
  exact congrFun (hremove (noise row)) col

/-- **A row-wise inverse lifts to the matrices it acts on.**

Both directions below are this one fact.  `rightWhiten` and `rightColor` are both
`rightTransform` -- two names for one operation, kept because the whitening story reads
better with both -- so "recoloring undoes whitening" and "whitening undoes recoloring" are
the same lemma with its two matrices exchanged, and each was carrying its own copy of the
three-line lift. -/
theorem rightTransform_leftInverse
    (outer inner : Matrix cols cols ℝ)
    (h : Function.LeftInverse
      (fun x ↦ outer.transpose.mulVec x)
      (fun x ↦ inner.transpose.mulVec x)) :
    Function.LeftInverse (rightTransform outer : Matrix rows cols ℝ → Matrix rows cols ℝ)
      (rightTransform inner) := by
  intro data
  ext row col
  exact congrFun (h (data row)) col

/-- Recoloring is a left inverse of whitening whenever the corresponding row
maps are inverse in that direction. -/
theorem rightColor_leftInverse_rightWhiten
    (color inverseColor : Matrix cols cols ℝ)
    (hleft : Function.LeftInverse
      (fun x ↦ color.transpose.mulVec x)
      (fun x ↦ inverseColor.transpose.mulVec x)) :
    Function.LeftInverse (rightColor color : Matrix rows cols ℝ → Matrix rows cols ℝ)
      (rightWhiten inverseColor) :=
  rightTransform_leftInverse color inverseColor hleft

/-- Recoloring is a right inverse of whitening whenever the corresponding row
maps are inverse in the other direction. -/
theorem rightColor_rightInverse_rightWhiten
    (color inverseColor : Matrix cols cols ℝ)
    (hright : Function.RightInverse
      (fun x ↦ color.transpose.mulVec x)
      (fun x ↦ inverseColor.transpose.mulVec x)) :
    Function.RightInverse (rightColor color : Matrix rows cols ℝ → Matrix rows cols ℝ)
      (rightWhiten inverseColor) :=
  -- `RightInverse f g` is `LeftInverse g f`, so this is the lift above with the two
  -- matrices exchanged rather than a second lift.
  rightTransform_leftInverse inverseColor color hright

/-- An invertible right-whitening map is a distribution-independent bijection
of data spaces, with recoloring as its explicit inverse. -/
theorem rightWhiten_bijective
    (color inverseColor : Matrix cols cols ℝ)
    (hleft : Function.LeftInverse
      (fun x ↦ color.transpose.mulVec x)
      (fun x ↦ inverseColor.transpose.mulVec x))
    (hright : Function.RightInverse
      (fun x ↦ color.transpose.mulVec x)
      (fun x ↦ inverseColor.transpose.mulVec x)) :
    Function.Bijective (rightWhiten inverseColor :
      Matrix rows cols ℝ → Matrix rows cols ℝ) := by
  have hmatrixLeft := rightColor_leftInverse_rightWhiten
    (rows := rows) color inverseColor hleft
  have hmatrixRight := rightColor_rightInverse_rightWhiten
    (rows := rows) color inverseColor hright
  exact ⟨hmatrixLeft.injective, hmatrixRight.surjective⟩

end Descent.Spectral
