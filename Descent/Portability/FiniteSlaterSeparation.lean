/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
The separation argument underlying Decision-Directed Portability, Theorem 14.
Convex finite constraint images are enlarged by strict coordinate slack.
Separation from zero produces an actual nonzero nonnegative multiplier vector
and a supporting inequality on every original feasible-domain point.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteSlaterSeparation

open Filter
open scoped BigOperators Topology

variable {A ι : Type*} [AddCommGroup A] [Module ℝ A] [Fintype ι] [DecidableEq ι]

/-- The strict upper image of the objective and constraint residuals. -/
def upperImage (C : Set A) (F : A → ι → ℝ) : Set (ι → ℝ) :=
  {y | ∃ x ∈ C, ∀ i, F x i < y i}

/-- A finite strict upper image is open, with no continuity of the parameterization required. -/
theorem upperImage_open (C : Set A) (F : A → ι → ℝ) : IsOpen (upperImage C F) := by
  have he : upperImage C F = ⋃ x ∈ C, ⋂ i, {y : ι → ℝ | F x i < y i} := by
    ext y
    simp [upperImage]
  rw [he]
  apply isOpen_iUnion
  intro x
  apply isOpen_iUnion
  intro _
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt continuous_const (continuous_apply i)

/-- Coordinatewise convexity makes the entire strict upper image convex. -/
theorem upperImage_convex (C : Set A) (F : A → ι → ℝ)
    (hC : Convex ℝ C) (hF : ∀ i, ConvexOn ℝ C (fun x ↦ F x i)) :
    Convex ℝ (upperImage C F) := by
  rintro y ⟨x, hx, hxy⟩ z ⟨v, hv, hvz⟩ α β hα hβ hsum
  refine ⟨α • x + β • v, hC hx hv hα hβ hsum, ?_⟩
  intro i
  have hconv := (hF i).2 hx hv hα hβ hsum
  change F (α • x + β • v) i ≤ α * F x i + β * F v i at hconv
  change F (α • x + β • v) i < α * y i + β * z i
  rcases eq_or_lt_of_le hα with hz | hp
  · have ha : α = 0 := hz.symm
    have hb : β = 1 := by linarith
    rw [ha, hb] at hconv ⊢
    simpa using hconv.trans_lt (by simpa using hvz i)
  · have h₁ := mul_lt_mul_of_pos_left (hxy i) hp
    have h₂ := mul_le_mul_of_nonneg_left (hvz i).le hβ
    linarith

/-- A continuous linear separator is exactly the finite pairing with its coordinate values. -/
theorem coordinate_pairing (L : (ι → ℝ) →L[ℝ] ℝ) (y : ι → ℝ) :
    L y = ∑ i, L (Pi.single i 1) * y i := by
  classical
  have he : y = ∑ i, y i • (Pi.single i (1 : ℝ) : ι → ℝ) := by
    ext j
    simp
  rw [he, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul, mul_comm]

/-- Every coordinate of an upward-set separator is nonnegative. -/
theorem coefficient_nonneg (C : Set A) (F : A → ι → ℝ) (hne : C.Nonempty)
    (L : (ι → ℝ) →L[ℝ] ℝ) (hL : ∀ y ∈ upperImage C F, 0 < L y) (i : ι) :
    0 ≤ L (Pi.single i 1) := by
  classical
  obtain ⟨x, hx⟩ := hne
  let y : ι → ℝ := fun j ↦ F x j + 1
  have hy : y ∈ upperImage C F := ⟨x, hx, fun j ↦ by dsimp [y]; linarith⟩
  have hpos := hL y hy
  by_contra hneg
  have hc : L (Pi.single i 1) < 0 := lt_of_not_ge hneg
  let t := -(L y + 1) / L (Pi.single i 1)
  have ht : 0 < t := div_pos_of_neg_of_neg (by linarith) hc
  have hnew : y + t • (Pi.single i (1 : ℝ) : ι → ℝ) ∈ upperImage C F := by
    refine ⟨x, hx, ?_⟩
    intro j
    have hj : (0 : ℝ) ≤ (Pi.single i (1 : ℝ) : ι → ℝ) j := by
      by_cases hij : i = j <;> simp [Pi.single_apply, hij]
    change F x j < y j + t * (Pi.single i (1 : ℝ) : ι → ℝ) j
    have hxy : F x j < y j := by dsimp [y]; linarith
    exact hxy.trans_le (le_add_of_nonneg_right (mul_nonneg ht.le hj))
  have hh := hL _ hnew
  rw [map_add, map_smul, smul_eq_mul] at hh
  have he : t * L (Pi.single i 1) = -(L y + 1) := div_mul_cancel₀ _ hc.ne
  rw [he] at hh
  linarith

/-- Taking vanishing positive slack extends the separator to the original constraint image. -/
theorem supporting_boundary (C : Set A) (F : A → ι → ℝ)
    (L : (ι → ℝ) →L[ℝ] ℝ) (hL : ∀ y ∈ upperImage C F, 0 < L y)
    (x : A) (hx : x ∈ C) : 0 ≤ L (F x) := by
  have ht : Tendsto (fun n : ℕ ↦ F x + (1 / ((n : ℝ) + 1)) • (fun _ : ι ↦ (1 : ℝ)))
      atTop (𝓝 (F x)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have hscalar := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ F x i) atTop (𝓝 (F x i))).add
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using hscalar
  apply ge_of_tendsto (L.continuous.tendsto (F x) |>.comp ht)
  apply Eventually.of_forall
  intro n
  apply (hL _ ?_).le
  refine ⟨x, hx, ?_⟩
  intro i
  change F x i < F x i + (1 / ((n : ℝ) + 1)) * 1
  have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-- Convex separation constructs a nonzero nonnegative finite multiplier vector. -/
theorem exists_nonnegative_separator (C : Set A) (F : A → ι → ℝ)
    (hC : Convex ℝ C) (hne : C.Nonempty) (hF : ∀ i, ConvexOn ℝ C (fun x ↦ F x i))
    (hzero : (0 : ι → ℝ) ∉ upperImage C F) :
    ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ (∃ i, 0 < a i) ∧
      ∀ x ∈ C, 0 ≤ ∑ i, a i * F x i := by
  classical
  obtain ⟨L, hL⟩ := geometric_hahn_banach_point_open
    (upperImage_convex C F hC hF) (upperImage_open C F) hzero
  simp only [map_zero] at hL
  let a (i : ι) := L (Pi.single i 1)
  have ha (i : ι) : 0 ≤ a i := coefficient_nonneg C F hne L hL i
  refine ⟨a, ha, ?_, ?_⟩
  · by_contra hnone
    push_neg at hnone
    have hz (i : ι) : a i = 0 := le_antisymm (hnone i) (ha i)
    obtain ⟨x, hx⟩ := hne
    have hh := hL (fun i ↦ F x i + 1) ⟨x, hx, fun i ↦ by linarith⟩
    rw [coordinate_pairing] at hh
    change 0 < ∑ i, a i * (F x i + 1) at hh
    simp only [hz, zero_mul, Finset.sum_const_zero] at hh
    exact (lt_irrefl 0) hh
  · intro x hx
    have hh := supporting_boundary C F L hL x hx
    rwa [coordinate_pairing] at hh

end Descent.Portability.FiniteSlaterSeparation
