/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ArchaicPrediction.Moments
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

assert_below Descent.Decision Descent.Program

/-!
# Additive export under arbitrary linkage disequilibrium

Equation (3.13). All moments are finite expectations under the current law.
The features can be arbitrarily dependent. Centering them makes the Gram
matrix a covariance and the response anchors cross-covariances. Nonsingularity
is explicit; a ridge penalty is not silently inserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchaicPrediction

open scoped BigOperators Matrix
variable {H I J : Type*} [Fintype H] [Fintype I] [DecidableEq I] [Fintype J]

noncomputable def centeredFeatures (w : H → ℝ) (X : I → H → ℝ) (i : I) (h : H) : ℝ :=
  X i h - weightedMean w (X i)

theorem centeredFeatures_mean (w : H → ℝ) (hw : ∑ h, w h = 1) (X : I → H → ℝ) (i : I) :
    weightedMean w (centeredFeatures w X i) = 0 := by
  change weightedMean w (fun h => X i h - weightedMean w (X i)) = 0
  rw [weightedMean_sub, weightedMean_const w hw, sub_self]

noncomputable def regressionGram (w : H → ℝ) (X : I → H → ℝ) : Matrix I I ℝ :=
  fun i j => weightedMean w (fun h => X i h * X j h)

noncomputable def regressionAnchor (w : H → ℝ) (X : I → H → ℝ) (f : H → ℝ) : I → ℝ :=
  fun i => weightedMean w (fun h => X i h * f h)

noncomputable def regressionScore (X : I → H → ℝ) (b : I → ℝ) (h : H) : ℝ := ∑ i, b i * X i h

noncomputable def exportedSlopes (w : H → ℝ) (X : I → H → ℝ) (f : H → ℝ) : I → ℝ :=
  (regressionGram w X)⁻¹ *ᵥ regressionAnchor w X f

theorem export_normal_equations (w : H → ℝ) (X : I → H → ℝ) (f : H → ℝ)
    (hdet : IsUnit (regressionGram w X).det) :
    regressionGram w X *ᵥ exportedSlopes w X f = regressionAnchor w X f := by
  rw [exportedSlopes, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- The numerator of the export formula retains every response monomial. -/
theorem response_anchor_expansion (w : H → ℝ) (X : I → H → ℝ) (θ : J → ℝ) (φ : J → H → ℝ) :
    regressionAnchor w X (fun h => ∑ j, θ j * φ j h) =
      fun i => ∑ j, θ j * weightedMean w (fun h => X i h * φ j h) := by
  funext i
  simp only [regressionAnchor, Finset.mul_sum]
  rw [weightedMean_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← weightedMean_scale]
  congr 1
  funext h
  ring

lemma export_residual_orthogonal (w : H → ℝ) (X : I → H → ℝ) (f : H → ℝ)
    (hdet : IsUnit (regressionGram w X).det) (i : I) :
    weightedMean w (fun h => X i h * (f h - regressionScore X (exportedSlopes w X f) h)) = 0 := by
  have hn := congrFun (export_normal_equations w X f hdet) i
  have hex (h : H) : X i h * regressionScore X (exportedSlopes w X f) h =
      ∑ j, exportedSlopes w X f j * (X i h * X j h) := by
    simp only [regressionScore, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros; ring
  simp_rw [mul_sub, weightedMean_sub, hex, weightedMean_sum, weightedMean_scale]
  change regressionAnchor w X f i - _ = 0
  change (∑ j, regressionGram w X i j * exportedSlopes w X f j) = regressionAnchor w X f i at hn
  simpa only [regressionGram, mul_comm, sub_eq_zero] using hn.symm

/-- The exported coefficients minimize squared error for the correlated feature law. -/
theorem arbitrary_ld_additive_optimum (w : H → ℝ) (hw : ∀ h, 0 ≤ w h)
    (X : I → H → ℝ) (f : H → ℝ) (hdet : IsUnit (regressionGram w X).det) (b : I → ℝ) :
    weightedMean w (fun h => (f h - regressionScore X (exportedSlopes w X f) h) ^ 2) ≤
      weightedMean w (fun h => (f h - regressionScore X b h) ^ 2) := by
  let best := exportedSlopes w X f
  let residual := fun h => f h - regressionScore X best h
  let changeScore := fun h => regressionScore X (best - b) h
  have ho : weightedMean w (fun h => residual h * changeScore h) = 0 := by
    have hex (h : H) : residual h * changeScore h =
        ∑ i, (best i - b i) * (X i h * residual h) := by
      dsimp [changeScore, regressionScore]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros; ring
    simp_rw [hex, weightedMean_sum, weightedMean_scale]
    simp only [residual, best, export_residual_orthogonal w X f hdet, mul_zero, Finset.sum_const_zero]
  have hex (h : H) : (f h - regressionScore X b h) ^ 2 =
      residual h ^ 2 + changeScore h ^ 2 + 2 * (residual h * changeScore h) := by
    have hs : changeScore h = regressionScore X best h - regressionScore X b h := by
      simp [changeScore, regressionScore, sub_mul, Finset.sum_sub_distrib]
    rw [hs]
    dsimp [residual]
    ring
  simp_rw [hex, weightedMean_add, weightedMean_scale, ho, mul_zero, add_zero]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun h _ => mul_nonneg (hw h) (sq_nonneg _))

/-- Equation (3.13), with the inverse covariance and all higher-order anchors explicit. -/
theorem arbitrary_ld_export_formula (w : H → ℝ) (X : I → H → ℝ)
    (θ : J → ℝ) (φ : J → H → ℝ) :
    exportedSlopes w (centeredFeatures w X) (fun h => ∑ j, θ j * φ j h) =
      (regressionGram w (centeredFeatures w X))⁻¹ *ᵥ
        (fun i => ∑ j, θ j * weightedMean w (fun h => centeredFeatures w X i h * φ j h)) := by
  rw [exportedSlopes, response_anchor_expansion]

end Descent.Portability.ArchaicPrediction
