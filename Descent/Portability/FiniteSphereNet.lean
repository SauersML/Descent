/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
The finite cover underlying Decision-Directed Portability, Theorem 10.
A maximal half-separated subset of the unit ball has at most 5^dimension
points by the proved volume packing bound. It controls every inner-product
direction with factor two, including in dimension zero. The cover is used
only in the proof, not enumerated by the proposed audit algorithm.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteSphereNet

section Packing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A half-separated finite subset of the unit ball. -/
def HalfPacking (s : Finset E) : Prop :=
  (∀ u ∈ s, ‖u‖ ≤ 1) ∧ ∀ u ∈ s, ∀ v ∈ s, u ≠ v → (1 : ℝ) / 2 ≤ ‖u - v‖

omit [FiniteDimensional ℝ E] in
/-- Scaling by two preserves distinct points. -/
theorem double_injective : Function.Injective (fun u : E ↦ (2 : ℝ) • u) := by
  intro u v h
  have hh := congrArg (fun z : E ↦ (1 / 2 : ℝ) • z) h
  simpa only [smul_smul, one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0), one_smul] using hh

/-- The actual volume-packing theorem gives the exact 5^dimension cardinal bound. -/
theorem packing_card_bound (s : Finset E) (hs : HalfPacking s) :
    s.card ≤ 5 ^ Module.finrank ℝ E := by
  classical
  let t := s.image (fun u ↦ (2 : ℝ) • u)
  have hn (c : E) (hc : c ∈ t) : ‖c‖ ≤ 2 := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hc
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hh := hs.1 u hu
    linarith
  have hsep (c : E) (hc : c ∈ t) (d : E) (hd : d ∈ t) (hcd : c ≠ d) :
      1 ≤ ‖c - d‖ := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hd
    have huv : u ≠ v := by intro he; apply hcd; rw [he]
    have hh := hs.2 u hu v hv huv
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hh := Besicovitch.card_le_of_separated t hn hsep
  dsimp [t] at hh
  rwa [Finset.card_image_of_injective s double_injective] at hh

/-- A largest finite packing exists because its cardinalities have a proved finite upper bound. -/
theorem exists_maximum_packing :
    ∃ s : Finset E, HalfPacking s ∧ ∀ t : Finset E, HalfPacking t → t.card ≤ s.card := by
  let A : Set ℕ := {n | ∃ s : Finset E, HalfPacking s ∧ s.card = n}
  have hne : A.Nonempty := by
    refine ⟨0, ∅, ?_, rfl⟩
    simp [HalfPacking]
  have hbound : BddAbove A := by
    refine ⟨5 ^ Module.finrank ℝ E, ?_⟩
    rintro n ⟨s, hs, rfl⟩
    exact packing_card_bound s hs
  obtain ⟨s, hs, hcard⟩ := Nat.sSup_mem hne hbound
  refine ⟨s, hs, ?_⟩
  intro t ht
  rw [hcard]
  exact le_csSup hbound ⟨t, ht, rfl⟩

/-- A maximum-cardinality packing covers the unit ball within distance one half. -/
theorem maximum_packing_covers (s : Finset E) (hs : HalfPacking s)
    (hmax : ∀ t : Finset E, HalfPacking t → t.card ≤ s.card) (x : E) (hx : ‖x‖ ≤ 1) :
    ∃ a ∈ s, ‖x - a‖ < (1 : ℝ) / 2 := by
  classical
  by_contra hn
  push_neg at hn
  have hnot : x ∉ s := by
    intro hmem
    have hh := hn x hmem
    norm_num at hh
  have hins : HalfPacking (insert x s) := by
    constructor
    · intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hx
      · exact hs.1 u hu
    · intro u hu v hv hne
      rcases Finset.mem_insert.mp hu with hux | hus
      · subst u
        rcases Finset.mem_insert.mp hv with hvx | hvs
        · exact (hne hvx.symm).elim
        · exact hn v hvs
      · rcases Finset.mem_insert.mp hv with hvx | hvs
        · subst v
          simpa only [norm_sub_rev] using hn u hus
        · exact hs.2 u hus v hvs hne
  have hc := hmax (insert x s) hins
  rw [Finset.card_insert_of_notMem hnot] at hc
  omega

/-- A nonempty finite half-net exists with the exact size bound used in the confidence exponent. -/
theorem exists_half_net :
    ∃ s : Finset E, s.Nonempty ∧ s.card ≤ 5 ^ Module.finrank ℝ E ∧
      (∀ a ∈ s, ‖a‖ ≤ 1) ∧ ∀ x, ‖x‖ ≤ 1 → ∃ a ∈ s, ‖x - a‖ < (1 : ℝ) / 2 := by
  obtain ⟨s, hs, hmax⟩ := exists_maximum_packing (E := E)
  have hcover := maximum_packing_covers s hs hmax
  have hne : s.Nonempty := by
    obtain ⟨a, ha, _⟩ := hcover 0 (by simp)
    exact ⟨a, ha⟩
  exact ⟨s, hne, packing_card_bound s hs, hs.1, hcover⟩

end Packing

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Controlling the finite net controls every direction, with the exact factor two. -/
theorem norm_le_twice (s : Finset E)
    (hcover : ∀ x : E, ‖x‖ ≤ 1 → ∃ a ∈ s, ‖x - a‖ < (1 : ℝ) / 2)
    (z : E) (b : ℝ) (hb : 0 ≤ b) (ha : ∀ a ∈ s, |inner ℝ a z| ≤ b) :
    ‖z‖ ≤ 2 * b := by
  by_cases hz : z = 0
  · simp only [hz, norm_zero]
    positivity
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    let u := (1 / ‖z‖) • z
    have hu : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hn)]
      exact one_div_mul_cancel hn.ne'
    obtain ⟨a, has, hdist⟩ := hcover u hu.le
    have hip : inner ℝ u z = ‖z‖ := by
      dsimp [u]
      rw [inner_smul_left, real_inner_self_eq_norm_sq]
      simp only [conj_trivial]
      field_simp [hn.ne']
    have hc := real_inner_le_norm (u - a) z
    rw [inner_sub_left, hip] at hc
    have hd := mul_le_mul_of_nonneg_right hdist.le (norm_nonneg z)
    have hh := (le_abs_self (inner ℝ a z)).trans (ha a has)
    nlinarith

end InnerProduct

end Descent.Portability.FiniteSphereNet
