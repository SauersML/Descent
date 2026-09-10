/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SamplingDesignLaw

assert_below Descent.Decision Descent.Program

/-!
The simulator samples the training deme before ancestry, allocating 5000
individuals there and 250 in every other deme. This source choice also controls
which plotted distances exist. The line and square-grid availability laws below
are exact before any additional conditioning on a reportable run.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SourceDesignLaw

open FiniteReportLaw SamplingDesignLaw

noncomputable def sourceLaw (demes : ℕ) (h : 0 < demes) : FiniteReportLaw (Fin demes) := by
  letI : Nonempty (Fin demes) := ⟨⟨0, h⟩⟩
  exact uniform _

theorem sourceLaw_mass (demes : ℕ) (h : 0 < demes) (source : Fin demes) :
    (sourceLaw demes h).mass source = 1 / (demes : ℝ) := by
  simp [sourceLaw, uniform]

/-- This allocation is an input to the ancestry sample state, rather than a
post-hoc relabeling of an ancestry draw with fixed per-deme sample counts. -/
def sampleSize {demes : ℕ} (source deme : Fin demes) : ℕ :=
  if deme = source then 5000 else 250

theorem sampleSize_total {demes : ℕ} (source : Fin demes) :
    (∑ deme, sampleSize source deme) = demes * 250 + 4750 := by
  have heq (deme : Fin demes) : sampleSize source deme =
      250 + if deme = source then 4750 else 0 := by
    by_cases h : deme = source <;> simp [sampleSize, h]
  simp_rw [heq]
  simp [Finset.sum_add_distrib]

def serialDistance {demes : ℕ} (source target : Fin demes) : ℕ :=
  (source.val - target.val) + (target.val - source.val)

def serialRadius {demes : ℕ} (source : Fin demes) : ℕ :=
  max source.val (demes - 1 - source.val)

/-- Every integer distance up to the more distant line endpoint occurs. -/
theorem serial_available_iff {demes : ℕ} (source : Fin demes) (distance : ℕ) :
    (∃ target, serialDistance source target = distance) ↔ distance ≤ serialRadius source := by
  have hs := source.isLt
  constructor
  · rintro ⟨target, ht⟩
    have htarget := target.isLt
    unfold serialDistance at ht
    unfold serialRadius
    omega
  · intro hd
    unfold serialRadius at hd
    by_cases hl : distance ≤ source.val
    · refine ⟨⟨source.val - distance, by omega⟩, ?_⟩
      dsimp only [serialDistance]
      omega
    · refine ⟨⟨source.val + distance, by omega⟩, ?_⟩
      dsimp only [serialDistance]
      omega

def gridDistance {side : ℕ} (source target : Fin side × Fin side) : ℕ :=
  serialDistance source.1 target.1 + serialDistance source.2 target.2

def gridRadius {side : ℕ} (source : Fin side × Fin side) : ℕ :=
  serialRadius source.1 + serialRadius source.2

/-- Manhattan distances on the square grid fill the interval from zero to
the farthest corner's distance. -/
theorem grid_available_iff {side : ℕ} (source : Fin side × Fin side) (distance : ℕ) :
    (∃ target, gridDistance source target = distance) ↔ distance ≤ gridRadius source := by
  constructor
  · rintro ⟨target, ht⟩
    have hr := (serial_available_iff source.1 (serialDistance source.1 target.1)).mp
      ⟨target.1, rfl⟩
    have hc := (serial_available_iff source.2 (serialDistance source.2 target.2)).mp
      ⟨target.2, rfl⟩
    unfold gridDistance at ht
    unfold gridRadius
    omega
  · intro hd
    let dr := min distance (serialRadius source.1)
    let dc := distance - dr
    have hr : dr ≤ serialRadius source.1 := Nat.min_le_right _ _
    have hc : dc ≤ serialRadius source.2 := by
      unfold dr dc gridRadius at *
      omega
    obtain ⟨row, hrow⟩ := (serial_available_iff source.1 dr).mpr hr
    obtain ⟨column, hcolumn⟩ := (serial_available_iff source.2 dc).mpr hc
    refine ⟨(row, column), ?_⟩
    change serialDistance source.1 row + serialDistance source.2 column = distance
    rw [hrow, hcolumn]
    unfold dr dc
    omega

/-- Source weights for the presence of a distance bin, before reportability
conditioning. They need not be equal across distances. -/
def serialSourceCount (demes distance : ℕ) : ℕ :=
  (Finset.univ.filter (fun source : Fin demes ↦ distance ≤ serialRadius source)).card

def gridSourceCount (side distance : ℕ) : ℕ :=
  (Finset.univ.filter (fun source : Fin side × Fin side ↦ distance ≤ gridRadius source)).card

theorem serialSourceCount_default :
    (List.range 11).map (serialSourceCount 10) = [10, 10, 10, 10, 10, 10, 8, 6, 4, 2, 0] := by
  decide

theorem gridSourceCount_default :
    (List.range 12).map (gridSourceCount 6) = [36, 36, 36, 36, 36, 36, 36, 32, 24, 12, 4, 0] := by
  decide

theorem serialSourceCount_mass (demes distance : ℕ) (h : 0 < demes) :
    (sourceLaw demes h).expectation
      (fun source ↦ if distance ≤ serialRadius source then 1 else 0) =
      serialSourceCount demes distance / (demes : ℝ) := by
  unfold expectation
  simp_rw [sourceLaw_mass]
  rw [← Finset.mul_sum]
  have hs : (∑ source : Fin demes, if distance ≤ serialRadius source then (1 : ℝ) else 0) =
      serialSourceCount demes distance := by
    simp [serialSourceCount, Finset.sum_boole]
  rw [hs]
  ring

/-- The uniform row-column law is the finite uniform training-cell law of
`grid2d`, using the bijection from row-major integer labels to grid cells. -/
noncomputable def gridSourceLaw (side : ℕ) (h : 0 < side) :
    FiniteReportLaw (Fin side × Fin side) := by
  letI : Nonempty (Fin side) := ⟨⟨0, h⟩⟩
  exact uniform _


/-- The row-major integer source draw and the row-column source draw have
exactly the same finite law under the simulator's grid indexing. -/
theorem gridSourceLaw_eq_integer_draw (side : ℕ) (h : 0 < side) :
    gridSourceLaw side h =
      (sourceLaw (side * side) (Nat.mul_pos h h)).pushforward finProdFinEquiv.symm := by
  classical
  apply FiniteReportLaw.ext
  intro source
  have heq (index : Fin (side * side)) :
      source = finProdFinEquiv.symm index ↔ index = finProdFinEquiv source := by
    rw [Equiv.eq_symm_apply]
    exact eq_comm
  simp only [pushforward, FiniteReportLaw.bind, pointMass, sourceLaw_mass, heq]
  simp [gridSourceLaw, uniform, Fintype.card_prod, Nat.cast_mul]

theorem gridSourceCount_mass (side distance : ℕ) (h : 0 < side) :
    (gridSourceLaw side h).expectation
      (fun source ↦ if distance ≤ gridRadius source then 1 else 0) =
      gridSourceCount side distance / (side * side : ℝ) := by
  letI : Nonempty (Fin side) := ⟨⟨0, h⟩⟩
  unfold gridSourceLaw
  rw [uniform_expectation]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  congr 1
  simp [gridSourceCount, Finset.sum_boole]

end Descent.Portability.SourceDesignLaw
