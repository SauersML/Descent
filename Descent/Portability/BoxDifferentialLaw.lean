/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CrossCoordinateRigidityLaw
import Descent.Portability.RadialPotentialLaw

assert_below Descent.Decision Descent.Program

/-!
The original open-box differential hypotheses for diploid effect fields. Joint
C² regularity is restricted to coordinate slices, and the closedness and own
second-derivative conditions imply exact separate quadraticity of every component.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BoxDifferentialLaw

open Set CrossCoordinateRigidityLaw QuadraticRigidityLaw

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- A genuine open rectangular box, with no boundary frequency values required. -/
def InBox (lo hi p : D → ℝ) : Prop := ∀ i, p i ∈ Ioo (lo i) (hi i)

def box (lo hi : D → ℝ) : Set (D → ℝ) := {p | InBox lo hi p}

noncomputable def coordinatePartial (f : (D → ℝ) → ℝ) (p : D → ℝ) (i : D) : ℝ :=
  deriv (fun x ↦ f (Function.update p i x)) (p i)

/-- The report's closedness condition, expressed using actual coordinate derivatives. -/
def ClosedOnBox (lo hi : D → ℝ) (b : D → (D → ℝ) → ℝ) : Prop :=
  ∀ p, InBox lo hi p → ∀ i j, coordinatePartial (b i) p j = coordinatePartial (b j) p i

/-- The report's own-coordinate second derivative vanishes at each point of the box. -/
def OwnAffineOnBox (lo hi : D → ℝ) (b : D → (D → ℝ) → ℝ) : Prop :=
  ∀ p, InBox lo hi p → ∀ i,
    deriv (deriv (fun x ↦ b i (Function.update p i x))) (p i) = 0

omit [Fintype D] in
theorem update_mem_box {lo hi p : D → ℝ} (hp : InBox lo hi p) (i : D)
    {x : ℝ} (hx : x ∈ Ioo (lo i) (hi i)) : InBox lo hi (Function.update p i x) := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa using hx
  · simpa [Function.update_of_ne hji] using hp j

omit [DecidableEq D] in
theorem box_isOpen (lo hi : D → ℝ) : IsOpen (box lo hi) := by
  have h : box lo hi = ⋂ i, (fun p : D → ℝ ↦ p i) ⁻¹' Ioo (lo i) (hi i) := by
    ext p
    simp [box, InBox]
  rw [h]
  exact isOpen_iInter_of_finite (fun i ↦ isOpen_Ioo.preimage (continuous_apply i))

/-- Joint smoothness on the box gives genuine interval smoothness of each slice. -/
theorem slice_contDiff {lo hi : D → ℝ} {f : (D → ℝ) → ℝ}
    (hf : ContDiffOn ℝ 2 f (box lo hi)) {p : D → ℝ} (hp : InBox lo hi p) (i : D) :
    ContDiffOn ℝ 2 (fun x ↦ f (Function.update p i x)) (Ioo (lo i) (hi i)) := by
  exact hf.comp (contDiff_update 2 p i).contDiffOn (fun x hx ↦ update_mem_box hp i hx)

omit [Fintype D] in
/-- Pointwise own-coordinate conditions imply vanishing second derivative on the entire slice. -/
theorem own_slice_second_zero {lo hi : D → ℝ} {b : D → (D → ℝ) → ℝ}
    (hown : OwnAffineOnBox lo hi b) {p : D → ℝ} (hp : InBox lo hi p) (i : D) :
    ∀ x ∈ Ioo (lo i) (hi i), deriv (deriv (fun t ↦ b i (Function.update p i t))) x = 0 := by
  intro x hx
  have h := hown (Function.update p i x) (update_mem_box hp i hx) i
  simpa only [Function.update_idem, Function.update_self] using h

/-- The own-coordinate field slice is exactly affine, with no polynomial assumption. -/
theorem own_slice_affine {lo hi : D → ℝ} {b : D → (D → ℝ) → ℝ}
    (hb : ∀ i, ContDiffOn ℝ 2 (b i) (box lo hi)) (hown : OwnAffineOnBox lo hi b)
    {p : D → ℝ} (hp : InBox lo hi p) (i : D) {s : ℝ}
    (hs : s ∈ Ioo (lo i) (hi i)) :
    ∀ x ∈ Ioo (lo i) (hi i), b i (Function.update p i x) =
      b i (Function.update p i s) +
        deriv (fun t ↦ b i (Function.update p i t)) s * (x - s) :=
  affine_of_second_derivative_zero _ hs (slice_contDiff (hb i) hp i)
    (own_slice_second_zero hown hp i)

omit [Fintype D] in
/-- Updating either coordinate of a two-coordinate slice has the expected exact effect. -/
theorem two_update_first (p : D → ℝ) {i j : D} (hij : i ≠ j) (x y u : ℝ) :
    Function.update (Function.update (Function.update p i x) j y) i u =
      Function.update (Function.update p i u) j y := by
  rw [Function.update_comm hij.symm, Function.update_idem]

/-- Closed C² fields with affine own slices have quadratic foreign slices. -/
theorem foreign_slice_quadratic {lo hi : D → ℝ} {b : D → (D → ℝ) → ℝ}
    (hb : ∀ i, ContDiffOn ℝ 2 (b i) (box lo hi))
    (hclosed : ClosedOnBox lo hi b) (hown : OwnAffineOnBox lo hi b)
    {p : D → ℝ} (hp : InBox lo hi p) {i j : D} (hij : i ≠ j)
    {s t : ℝ} (hs : s ∈ Ioo (lo j) (hi j)) (ht : t ∈ Ioo (lo j) (hi j))
    (hst : s ≠ t) :
    ∃ A B C : ℝ, ∀ y ∈ Ioo (lo j) (hi j),
      b i (Function.update p j y) = A + B * y + C * y ^ 2 := by
  let bi := fun x y ↦ b i (Function.update (Function.update p i x) j y)
  let bj := fun x y ↦ b j (Function.update (Function.update p i x) j y)
  have hjy : ∀ x ∈ Ioo (lo i) (hi i), ContDiffOn ℝ 2 (bj x) (Ioo (lo j) (hi j)) := by
    intro x hx
    exact slice_contDiff (hb j) (update_mem_box hp i hx) j
  have hjzero : ∀ x ∈ Ioo (lo i) (hi i), ∀ y ∈ Ioo (lo j) (hi j),
      deriv (deriv (bj x)) y = 0 := by
    intro x hx
    exact own_slice_second_zero hown (update_mem_box hp i hx) j
  have hjx : ∀ y ∈ Ioo (lo j) (hi j),
      DifferentiableOn ℝ (fun x ↦ bj x y) (Ioo (lo i) (hi i)) := by
    intro y hy
    have h := (slice_contDiff (hb j) (update_mem_box hp j hy) i).differentiableOn
      (by norm_num)
    simpa only [bj, Function.update_comm hij] using h
  have hiy : ∀ x ∈ Ioo (lo i) (hi i), DifferentiableOn ℝ (bi x) (Ioo (lo j) (hi j)) := by
    intro x hx
    exact (slice_contDiff (hb i) (update_mem_box hp i hx) j).differentiableOn (by norm_num)
  have hc : ∀ x ∈ Ioo (lo i) (hi i), ∀ y ∈ Ioo (lo j) (hi j),
      deriv (bi x) y = deriv (fun x ↦ bj x y) x := by
    intro x hx y hy
    have h := hclosed (Function.update (Function.update p i x) j y)
      (update_mem_box (update_mem_box hp i hx) j hy) i j
    simpa only [coordinatePartial, bi, bj, Function.update_idem, Function.update_self,
      Function.update_of_ne hij, two_update_first p hij] using h
  have hquad := closed_field_foreign_quadratic bi bj hs ht hst hjy hjzero hjx hiy hc (p i) (hp i)
  let c := (deriv (bi (p i)) t - deriv (bi (p i)) s) / (2 * (t - s))
  refine ⟨bi (p i) s - deriv (bi (p i)) s * s + c * s ^ 2,
    deriv (bi (p i)) s - 2 * c * s, c, ?_⟩
  intro y hy
  have h := hquad y hy
  rw [show b i (Function.update p j y) = bi (p i) y by simp [bi]]
  rw [h]
  dsimp only [c]
  ring

/-- The original C² compatibility conditions force every component to be separately quadratic. -/
theorem component_separately_quadratic {lo hi : D → ℝ} {b : D → (D → ℝ) → ℝ}
    (hb : ∀ i, ContDiffOn ℝ 2 (b i) (box lo hi))
    (hclosed : ClosedOnBox lo hi b) (hown : OwnAffineOnBox lo hi b)
    {p : D → ℝ} (hp : InBox lo hi p) (i j : D) :
    ∃ A B C : ℝ, ∀ y ∈ Ioo (lo j) (hi j),
      b i (Function.update p j y) = A + B * y + C * y ^ 2 := by
  by_cases hij : i = j
  · subst j
    let slope := deriv (fun t ↦ b i (Function.update p i t)) (p i)
    refine ⟨b i p - slope * p i, slope, 0, ?_⟩
    intro y hy
    have h := own_slice_affine hb hown hp i (hp i) y hy
    simp only [Function.update_eq_self] at h
    rw [h]
    dsimp only [slope]
    ring
  · have ht : (p j + hi j) / 2 ∈ Ioo (lo j) (hi j) := by
      constructor <;> linarith [(hp j).1, (hp j).2]
    have hst : p j ≠ (p j + hi j) / 2 := by linarith [(hp j).2]
    exact foreign_slice_quadratic hb hclosed hown hp hij (hp j) ht hst

end Descent.Portability.BoxDifferentialLaw
