/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.OperatorPositiveCone
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation

assert_below Descent.Decision Descent.Program

/-!
Separation for the actual spectral audit epigraph. The residual space has
two real coordinates and a bounded operator coordinate. Strict quadratic
slack makes its upper image open, and directional convexity makes it convex.
Hahn--Banach then supplies a positive functional on the entire operator cone,
not a finite selection of repair directions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.OperatorSlaterSeparation

open OperatorPositiveCone Filter
open scoped Topology

variable {X E : Type*} [AddCommGroup X] [Module ℝ X]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Objective, budget and operator residual coordinates. -/
abbrev ResidualSpace (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  ℝ × ℝ × (E →L[ℝ] E)

/-- The strict upper image uses uniform positive quadratic operator slack. -/
def upperImage (C : Set X) (F : X → ResidualSpace E) : Set (ResidualSpace E) :=
  {y | ∃ x ∈ C, (F x).1 < y.1 ∧ (F x).2.1 < y.2.1 ∧
    StrictPositive (y.2.2 - (F x).2.2)}

/-- Every fixed residual has an open strict upper slice. -/
theorem upperImage_open (C : Set X) (F : X → ResidualSpace E) :
    IsOpen (upperImage C F) := by
  have he : upperImage C F = ⋃ x ∈ C,
      {y : ResidualSpace E | (F x).1 < y.1} ∩
      ({y : ResidualSpace E | (F x).2.1 < y.2.1} ∩
      {y : ResidualSpace E | StrictPositive (y.2.2 - (F x).2.2)}) := by
    ext y
    simp [upperImage, and_assoc, and_left_comm, and_comm]
  rw [he]
  apply isOpen_iUnion
  intro x
  apply isOpen_iUnion
  intro _hx
  exact (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_const continuous_snd.fst).inter
      (strictPositive_open.preimage (continuous_snd.snd.sub continuous_const)))

/-- Convex residual components give a convex strict operator upper image. -/
theorem upperImage_convex (C : Set X) (F : X → ResidualSpace E)
    (hC : Convex ℝ C) (hf : ConvexOn ℝ C (fun x ↦ (F x).1))
    (hg : ConvexOn ℝ C (fun x ↦ (F x).2.1))
    (hH : ∀ v : E, ConvexOn ℝ C (fun x ↦ inner ℝ v ((F x).2.2 v))) :
    Convex ℝ (upperImage C F) := by
  rintro y ⟨x, hx, hxy, hxy', e, he, hA⟩ z ⟨v, hv, hvz, hvz', d, hd, hB⟩ a b ha hb hab
  have hs (u w c k q : ℝ) (hu : u < c) (hw : w < k) (hq : q ≤ a * u + b * w) :
      q < a * c + b * k := by
    rcases eq_or_lt_of_le ha with hz | hp
    · have ha0 : a = 0 := hz.symm
      have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hq.trans_lt (by simpa [ha0, hb1] using hw)
    · have h₁ := mul_lt_mul_of_pos_left hu hp
      have h₂ := mul_le_mul_of_nonneg_left hw.le hb
      linarith
  refine ⟨a • x + b • v, hC hx hv ha hb hab, ?_, ?_, a * e + b * d, ?_, ?_⟩
  · exact hs _ _ _ _ _ hxy hvz (hf.2 hx hv ha hb hab)
  · exact hs _ _ _ _ _ hxy' hvz' (hg.2 hx hv ha hb hab)
  · rcases eq_or_lt_of_le ha with hz | hp
    · have ha0 : a = 0 := hz.symm
      have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hd
    · exact add_pos_of_pos_of_nonneg (mul_pos hp he) (mul_nonneg hb hd.le)
  · intro q
    have h₁ := mul_le_mul_of_nonneg_left (hA q) ha
    have h₂ := mul_le_mul_of_nonneg_left (hB q) hb
    have h₃ := (hH q).2 hx hv ha hb hab
    change inner ℝ q ((F (a • x + b • v)).2.2 q) ≤
      a * inner ℝ q ((F x).2.2 q) + b * inner ℝ q ((F v).2.2 q) at h₃
    change (a * e + b * d) * ‖q‖ ^ 2 ≤
      inner ℝ q ((a • y.2.2 + b • z.2.2 - (F (a • x + b • v)).2.2) q)
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, inner_sub_right, inner_add_right,
      inner_smul_right] at h₁ h₂ ⊢
    nlinarith

/-- A nonnegative residual direction can be added with any nonnegative magnitude. -/
theorem upperImage_add (C : Set X) (F : X → ResidualSpace E) (y z : ResidualSpace E)
    (hy : y ∈ upperImage C F) (hz₀ : 0 ≤ z.1) (hz₁ : 0 ≤ z.2.1)
    (hz₂ : Nonnegative z.2.2) (t : ℝ) (ht : 0 ≤ t) :
    y + t • z ∈ upperImage C F := by
  obtain ⟨x, hx, h₀, h₁, h₂⟩ := hy
  refine ⟨x, hx, h₀.trans_le (le_add_of_nonneg_right (mul_nonneg ht hz₀)),
    h₁.trans_le (le_add_of_nonneg_right (mul_nonneg ht hz₁)), ?_⟩
  have hh := strict_add_nonnegative (y.2.2 - (F x).2.2) (t • z.2.2)
    h₂ (nonnegative_smul z.2.2 hz₂ t ht)
  convert hh using 1 <;> dsimp <;> congr 1 <;> abel

/-- The separator is nonnegative on every nonnegative scalar and operator direction. -/
theorem direction_nonneg (C : Set X) (F : X → ResidualSpace E)
    (hne : (upperImage C F).Nonempty) (L : ResidualSpace E →L[ℝ] ℝ)
    (hL : ∀ y ∈ upperImage C F, 0 < L y) (z : ResidualSpace E)
    (hz₀ : 0 ≤ z.1) (hz₁ : 0 ≤ z.2.1) (hz₂ : Nonnegative z.2.2) : 0 ≤ L z := by
  obtain ⟨y, hy⟩ := hne
  have hpos := hL y hy
  by_contra hn
  have hc : L z < 0 := lt_of_not_ge hn
  let t := -(L y + 1) / L z
  have ht : 0 < t := div_pos_of_neg_of_neg (by linarith) hc
  have hh := hL _ (upperImage_add C F y z hy hz₀ hz₁ hz₂ t ht.le)
  rw [map_add, map_smul, smul_eq_mul] at hh
  have he : t * L z = -(L y + 1) := div_mul_cancel₀ _ hc.ne
  rw [he] at hh
  linarith

/-- Positive slack in all coordinates approaches every original residual. -/
theorem shifted_mem (C : Set X) (F : X → ResidualSpace E) (x : X) (hx : x ∈ C)
    (e : ℝ) (he : 0 < e) :
    F x + e • (1, 1, ContinuousLinearMap.id ℝ E) ∈ upperImage C F := by
  refine ⟨x, hx, ?_, ?_, ?_⟩
  · change (F x).1 < (F x).1 + e * 1
    linarith
  · change (F x).2.1 < (F x).2.1 + e * 1
    linarith
  · change StrictPositive ((F x).2.2 + e • ContinuousLinearMap.id ℝ E - (F x).2.2)
    simpa only [add_sub_cancel_left] using strict_identity (E := E) e he

/-- Continuity extends the strict separator inequality to the original residual boundary. -/
theorem supporting_boundary (C : Set X) (F : X → ResidualSpace E)
    (L : ResidualSpace E →L[ℝ] ℝ) (hL : ∀ y ∈ upperImage C F, 0 < L y)
    (x : X) (hx : x ∈ C) : 0 ≤ L (F x) := by
  have ht : Tendsto (fun n : ℕ ↦ F x + (1 / ((n : ℝ) + 1)) •
      (1, 1, ContinuousLinearMap.id ℝ E)) atTop (𝓝 (F x)) := by
    have hs := tendsto_one_div_add_atTop_nhds_zero_nat.smul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦
        (1, 1, ContinuousLinearMap.id ℝ E)) atTop (𝓝 (1, 1, ContinuousLinearMap.id ℝ E)))
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ F x) atTop (𝓝 (F x))).add hs
  apply ge_of_tendsto (L.continuous.tendsto (F x) |>.comp ht)
  exact Eventually.of_forall (fun n ↦ (hL _ (shifted_mem C F x hx _ (by positivity))).le)

/-- The actual continuous separator exists for the full spectral residual space. -/
theorem exists_separator (C : Set X) (F : X → ResidualSpace E)
    (hC : Convex ℝ C) (hne : C.Nonempty) (hf : ConvexOn ℝ C (fun x ↦ (F x).1))
    (hg : ConvexOn ℝ C (fun x ↦ (F x).2.1))
    (hH : ∀ v : E, ConvexOn ℝ C (fun x ↦ inner ℝ v ((F x).2.2 v)))
    (hzero : (0 : ResidualSpace E) ∉ upperImage C F) :
    ∃ L : ResidualSpace E →L[ℝ] ℝ,
      (∀ y ∈ upperImage C F, 0 < L y) ∧
      (∀ z, 0 ≤ z.1 → 0 ≤ z.2.1 → Nonnegative z.2.2 → 0 ≤ L z) ∧
      ∀ x ∈ C, 0 ≤ L (F x) := by
  obtain ⟨L, hL⟩ := geometric_hahn_banach_point_open
    (upperImage_convex C F hC hf hg hH) (upperImage_open C F) hzero
  simp only [map_zero] at hL
  obtain ⟨x, hx⟩ := hne
  have hu : (upperImage C F).Nonempty := ⟨_, shifted_mem C F x hx 1 zero_lt_one⟩
  exact ⟨L, hL, direction_nonneg C F hu L hL, supporting_boundary C F L hL⟩

end Descent.Portability.OperatorSlaterSeparation
