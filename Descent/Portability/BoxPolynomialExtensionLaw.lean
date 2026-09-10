/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BoxDifferentialLaw
import Descent.Portability.TensorInterpolationLaw

assert_below Descent.Decision Descent.Program

/-!
An explicit smooth polynomial extension of a compatible C² field from an open
box. Interior interpolation nodes are constructed from the box bounds. The
extension and its coordinate derivatives agree with the original field on that
box; symmetry outside the box is neither assumed nor needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BoxPolynomialExtensionLaw

open Set BoxDifferentialLaw TensorInterpolationLaw DiploidBernsteinLaw RadialPotentialLaw

variable {n : ℕ}

/-- Three distinct interpolation nodes strictly inside each coordinate interval. -/
noncomputable def interiorNodes (lo hi : Fin n → ℝ) (i : Fin n) (k : Fin 3) : ℝ :=
  if k.val = 0 then (2 * lo i + hi i) / 3
  else if k.val = 1 then (lo i + hi i) / 2 else (lo i + 2 * hi i) / 3

theorem interiorNodes_mem (lo hi : Fin n → ℝ) (hwidth : ∀ i, lo i < hi i)
    (i : Fin n) (k : Fin 3) : interiorNodes lo hi i k ∈ Ioo (lo i) (hi i) := by
  fin_cases k <;> norm_num [interiorNodes] <;> constructor <;> linarith [hwidth i]

theorem interiorNodes_injective (lo hi : Fin n → ℝ) (hwidth : ∀ i, lo i < hi i)
    (i : Fin n) : Function.Injective (interiorNodes lo hi i) := by
  intro k l h
  fin_cases k <;> fin_cases l <;> norm_num [interiorNodes] at * <;> linarith [hwidth i]

/-- Every finite tensor quadratic is continuously differentiable on the entire real space. -/
theorem tensorQuadratic_contDiff (coeff : (Fin n → Fin 3) → ℝ) :
    ContDiff ℝ 1 (tensorQuadratic coeff) := by
  have hprod (d : Fin n → Fin 3) (s : Finset (Fin n)) :
      ContDiff ℝ 1 (fun p : Fin n → ℝ ↦ ∏ i ∈ s, p i ^ (d i).val) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using (contDiff_const (c := (1 : ℝ)))
    | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi] using ((contDiff_apply ℝ ℝ i).pow (d i).val).mul ih
  unfold tensorQuadratic
  apply ContDiff.sum
  intro d _
  exact contDiff_const.mul (hprod d _)

/-- The extension is determined completely by the original field's interior node values. -/
noncomputable def extension (lo hi : Fin n → ℝ) (b : Fin n → (Fin n → ℝ) → ℝ)
    (i : Fin n) : (Fin n → ℝ) → ℝ :=
  tensorQuadratic (interpolatedCoefficients (interiorNodes lo hi)
    (fun g ↦ b i (fun j ↦ interiorNodes lo hi j (g j))))

theorem extension_contDiff (lo hi : Fin n → ℝ) (b : Fin n → (Fin n → ℝ) → ℝ)
    (i : Fin n) : ContDiff ℝ 1 (extension lo hi b i) := tensorQuadratic_contDiff _

/-- The explicit global extension agrees with the original C² field everywhere on its box. -/
theorem extension_eq {lo hi : Fin n → ℝ} (hwidth : ∀ i, lo i < hi i)
    {b : Fin n → (Fin n → ℝ) → ℝ}
    (hb : ∀ i, ContDiffOn ℝ 2 (b i) (box lo hi))
    (hclosed : ClosedOnBox lo hi b) (hown : OwnAffineOnBox lo hi b)
    {p : Fin n → ℝ} (hp : InBox lo hi p) (i : Fin n) : extension lo hi b i p = b i p := by
  symm
  exact separately_quadratic_polynomial n (fun j ↦ Ioo (lo j) (hi j))
    (interiorNodes lo hi) (interiorNodes_mem lo hi hwidth) (interiorNodes_injective lo hi hwidth)
    (b i) (fun q hq j ↦ component_separately_quadratic hb hclosed hown hq i j) p hp

/-- Local equality on the box preserves actual coordinate derivatives. -/
theorem coordinatePartial_eq_of_box_eq {lo hi : Fin n → ℝ}
    {f g : (Fin n → ℝ) → ℝ} (hfg : ∀ p, InBox lo hi p → f p = g p)
    {p : Fin n → ℝ} (hp : InBox lo hi p) (j : Fin n) :
    coordinatePartial f p j = coordinatePartial g p j := by
  have h : EqOn (fun x ↦ f (Function.update p j x))
      (fun x ↦ g (Function.update p j x)) (Ioo (lo j) (hi j)) := by
    intro x hx
    exact hfg _ (update_mem_box hp j hx)
  exact h.deriv isOpen_Ioo (hp j)

/-- The coordinate derivative is the derivative linear map applied to its basis vector. -/
theorem coordinatePartial_eq_fderiv {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) (p : Fin n → ℝ) (j : Fin n) :
    coordinatePartial f p j = fderiv ℝ f p (basis j) := by
  have hd := ((hf.differentiable (by norm_num)) (Function.update p j (p j))).hasFDerivAt
  have h := hd.comp_hasDerivAt (p j) (update_hasDerivAt p j (p j))
  simpa only [coordinatePartial, Function.update_eq_self] using h.deriv

/-- The extension's Jacobian retains the report's symmetry on the original box. -/
theorem extension_closed {lo hi : Fin n → ℝ} (hwidth : ∀ i, lo i < hi i)
    {b : Fin n → (Fin n → ℝ) → ℝ}
    (hb : ∀ i, ContDiffOn ℝ 2 (b i) (box lo hi))
    (hclosed : ClosedOnBox lo hi b) (hown : OwnAffineOnBox lo hi b)
    {p : Fin n → ℝ} (hp : InBox lo hi p) (i j : Fin n) :
    fderiv ℝ (extension lo hi b i) p (basis j) =
      fderiv ℝ (extension lo hi b j) p (basis i) := by
  rw [← coordinatePartial_eq_fderiv (extension_contDiff lo hi b i),
    ← coordinatePartial_eq_fderiv (extension_contDiff lo hi b j)]
  rw [coordinatePartial_eq_of_box_eq (fun q hq ↦ extension_eq hwidth hb hclosed hown hq i) hp j,
    coordinatePartial_eq_of_box_eq (fun q hq ↦ extension_eq hwidth hb hclosed hown hq j) hp i]
  exact hclosed p hp i j

/-- Every point on the anchored segment remains strictly inside the open box. -/
theorem segment_mem_box {lo hi a p : Fin n → ℝ} (ha : InBox lo hi a) (hp : InBox lo hi p)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : InBox lo hi (segment a p t) := by
  intro i
  have h := convex_Ioo (𝕜 := ℝ) (lo i) (hi i) (ha i) (hp i)
    (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
  convert h using 1
  simp only [RadialPotentialLaw.segment, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- The explicit line integral has the required derivative for the original field. -/
theorem box_potential_hasDerivAt {lo hi : Fin n → ℝ} (hwidth : ∀ i, lo i < hi i)
    {b : Fin n → (Fin n → ℝ) → ℝ}
    (hb : ∀ i, ContDiffOn ℝ 2 (b i) (box lo hi))
    (hclosed : ClosedOnBox lo hi b) (hown : OwnAffineOnBox lo hi b)
    {a p : Fin n → ℝ} (ha : InBox lo hi a) (hp : InBox lo hi p) (j : Fin n) :
    HasDerivAt (fun x ↦ potential (extension lo hi b) a (Function.update p j x))
      (2 * b j p) (p j) := by
  have h := potential_coordinate_hasDerivAt (extension lo hi b) (extension_contDiff lo hi b)
    a p j (fun t ht i ↦ extension_closed hwidth hb hclosed hown (segment_mem_box ha hp ht) i j)
  simpa only [extension_eq hwidth hb hclosed hown hp j] using h

end Descent.Portability.BoxPolynomialExtensionLaw
