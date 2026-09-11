/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RealizationBody

assert_below Descent.Decision Descent.Program

/-!
# Carathéodory's count with a constant coordinate

NOTE1 §2.1 states that when one coordinate of a feature map is identically one, every point of
its realization body is the feature vector of a probability law with at most `k` atoms, `k`
the number of coordinates. `RealizationBody.exists_law_of_mem_realizationBody` proves the
ambient count `k + 1`. This module proves the count `k`.

The constant coordinate confines the body to an affine hyperplane, and the proof uses that in
the most direct way: it deletes the coordinate. `reducedFeature φ i₀` is the feature map with
the coordinate `i₀` removed, on `k - 1` coordinates by `card_reducedCoordinates`. A law that
realizes a point of the body realizes the point's projection under the reduced map
(`featureVector_reducedFeature`), so the ambient count for the reduced map gives a law on
`(k - 1) + 1 = k` atoms realizing that projection. The same law realizes the original point:
the deleted coordinate of its feature vector is its total mass, one, and every point of the
body has that coordinate equal to one by `constant_coordinate_eq`.

`exists_law_card_of_constant_coordinate` states the result in the same form as the ambient
count, as a law on `Fin (Fintype.card ι)`. Some atoms may carry zero weight, so the count is an
upper bound. That `k` atoms can be necessary is not formalized.

## Empirical status

None. The bodies here are finite combinatorics of a convex hull: deleting a coordinate and
counting indices. No measurement can bear on how many atoms a convex combination needs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AffineCaratheodoryCount

open Descent.Portability.FiniteMixtureKernel
open Descent.Portability.RealizationBody

noncomputable section

/-- The feature map with the coordinate `i₀` deleted: the same map read only at the remaining
coordinates. -/
def reducedFeature {X ι : Type*} [Fintype ι] [DecidableEq ι] (φ : X → ι → ℝ) (i₀ : ι) :
    X → ↥(Finset.univ.erase i₀) → ℝ :=
  fun x i ↦ φ x i

/-- Deleting one coordinate leaves exactly one coordinate fewer. -/
theorem card_reducedCoordinates {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) :
    Fintype.card ↥(Finset.univ.erase i₀) + 1 = Fintype.card ι := by
  rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ]
  have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i₀⟩
  omega

/-- The feature vector of a law under the reduced feature map is its feature vector under the
full map, read at the remaining coordinates. -/
theorem featureVector_reducedFeature {Ω X ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (p : Ω → ℝ) (point : Ω → X) (φ : X → ι → ℝ) (i₀ : ι) :
    featureVector p point (reducedFeature φ i₀)
      = fun i : ↥(Finset.univ.erase i₀) ↦ featureVector p point φ i := by
  funext i
  simp only [featureVector_apply, reducedFeature]

/-- **NOTE1 §2.1, Carathéodory's count with a constant coordinate.** If one coordinate of the
feature map is identically one, every point of the realization body is the feature vector of a
finitely supported probability law on `Fintype.card ι` atoms, one fewer than the ambient
count. -/
theorem exists_law_card_of_constant_coordinate {X ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : X → ι → ℝ) (i₀ : ι) (hconst : ∀ x, φ x i₀ = 1) (v : ι → ℝ)
    (hv : v ∈ realizationBody φ) :
    ∃ p : Fin (Fintype.card ι) → ℝ, ∃ point : Fin (Fintype.card ι) → X,
      (∀ k, 0 ≤ p k) ∧ ∑ k, p k = 1 ∧ featureVector p point φ = v := by
  obtain ⟨Ω, hΩ, p, point, hp, hsum, hfeat⟩ := (mem_realizationBody_iff φ v).mp hv
  have hreduced : (fun i : ↥(Finset.univ.erase i₀) ↦ v i)
      ∈ realizationBody (reducedFeature φ i₀) := by
    refine (mem_realizationBody_iff _ _).mpr ⟨Ω, hΩ, p, point, hp, hsum, ?_⟩
    rw [featureVector_reducedFeature p point φ i₀, hfeat]
  obtain ⟨q, atom, hq, hqsum, hqfeat⟩ :=
    exists_law_of_mem_realizationBody (reducedFeature φ i₀) _ hreduced
  have hlaw : ∃ q : Fin (Fintype.card ↥(Finset.univ.erase i₀) + 1) → ℝ,
      ∃ atom : Fin (Fintype.card ↥(Finset.univ.erase i₀) + 1) → X,
        (∀ k, 0 ≤ q k) ∧ ∑ k, q k = 1 ∧ featureVector q atom φ = v := by
    refine ⟨q, atom, hq, hqsum, ?_⟩
    funext i
    by_cases hi : i = i₀
    · rw [hi, constant_coordinate_eq φ i₀ hconst v hv, featureVector_apply]
      simpa [hconst] using hqsum
    · have hcoordinate := congrFun hqfeat ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩⟩
      rw [featureVector_reducedFeature q atom φ i₀] at hcoordinate
      exact hcoordinate
  rw [card_reducedCoordinates i₀] at hlaw
  exact hlaw

end

end Descent.Portability.AffineCaratheodoryCount
