/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GlobalFourthMomentRegion

assert_below Descent.Decision Descent.Program

/-!
# The score moment zonoid and the support-function criterion

UPT Theorem 3.2 states the constant-magnitude criterion twice: as membership of `(β, k)` in
`√m 𝒵_X`, where `𝒵_X = {E[(1, X) z] : |z| ≤ 1}` of (3.15), and equivalently as the family
of supporting-halfspace inequalities (3.17). `GlobalFourthMomentRegion` proves membership
implies the inequalities. This module proves the converse, which is the half that carries
the geometry.

For a finitely supported pre-outcome law, `𝒵_X` is the image of the cube `|z| ≤ 1` under a
linear map into `ℝ × ℝ^p`, hence compact and convex. A point outside it is strictly
separated from it by a continuous linear functional, and every such functional on
`ℝ × ℝ^p` is `(a, b) ↦ λ₀ a + λᵀ b`. The supremum of that functional over `𝒵_X` is
`E|λ₀ + λᵀX|`, attained at the measurable sign, so the separation contradicts (3.17)
exactly.

* `scoreZonoid` is `𝒵_X`; `momentMap_isLinear`, `isCompact_scoreZonoid` and
  `convex_scoreZonoid` are its geometry.
* `dual_representation` writes any continuous linear functional on `ℝ × ℝ^p` in the
  coordinates `(λ₀, λ)` the manuscript uses.
* `mem_scoreZonoid_of_support` is the converse of (3.17), and
  `exists_contraction_of_support_bound` states it as the existence of the contraction.
* `minFourthMoment_eq_sq_of_support` closes UPT Theorem 3.2 in the direction
  (3.17) ⟹ `V = m²`, by feeding that contraction to
  `GlobalFourthMomentRegion.constant_magnitude_value`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ScoreMomentZonoid

open Foundations IndividualLossMoments FourthMomentDuality GlobalFourthMomentRegion

noncomputable section

variable {Ω : Type*} [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The zonoid and its geometry -/

/-- The moment map of UPT (3.15): a contraction `z` is sent to `(E z, E[X z])`. -/
def momentMap (E : ExpFunctional Ω) (X : Ω → ι → ℝ) (z : Ω → ℝ) : ℝ × (ι → ℝ) :=
  (E z, fun i ↦ E (fun ω ↦ X ω i * z ω))

/-- The contractions `|z| ≤ 1` of UPT (3.15), as a product of intervals. -/
def contractionBox (Ω : Type*) : Set (Ω → ℝ) :=
  Set.univ.pi fun _ : Ω ↦ Set.Icc (-1) 1

/-- The set `𝒵_X` of UPT (3.15): the moment images of all contractions. -/
def scoreZonoid (E : ExpFunctional Ω) (X : Ω → ι → ℝ) : Set (ℝ × (ι → ℝ)) :=
  momentMap E X '' contractionBox Ω

omit [Fintype Ω] in
/-- Membership in the contraction box is the pointwise bound `|z| ≤ 1`. -/
theorem mem_contractionBox {z : Ω → ℝ} : z ∈ contractionBox Ω ↔ ∀ ω, |z ω| ≤ 1 := by
  unfold contractionBox
  rw [Set.mem_univ_pi]
  constructor
  · intro h ω
    exact abs_le.mpr ⟨(h ω).1, (h ω).2⟩
  · intro h ω
    exact ⟨(abs_le.mp (h ω)).1, (abs_le.mp (h ω)).2⟩

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
/-- The moment map is linear, so the zonoid is a linear image of a cube. -/
theorem momentMap_isLinear (E : ExpFunctional Ω) (X : Ω → ι → ℝ) :
    IsLinearMap ℝ (momentMap E X) := by
  constructor
  · intro z w
    have h1 : E (z + w) = E z + E w := E.add_eval z w
    have h2 : ∀ i, E (fun ω ↦ X ω i * (z + w) ω)
        = E (fun ω ↦ X ω i * z ω) + E (fun ω ↦ X ω i * w ω) := by
      intro i
      have hfun : (fun ω ↦ X ω i * (z + w) ω)
          = (fun ω ↦ X ω i * z ω) + (fun ω ↦ X ω i * w ω) := by
        funext ω
        simp only [Pi.add_apply]
        ring
      rw [hfun, E.add_eval]
    show (E (z + w), fun i ↦ E (fun ω ↦ X ω i * (z + w) ω))
      = (E z, fun i ↦ E (fun ω ↦ X ω i * z ω))
        + (E w, fun i ↦ E (fun ω ↦ X ω i * w ω))
    rw [Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨h1, funext fun i ↦ ?_⟩
    show E (fun ω ↦ X ω i * (z + w) ω)
      = E (fun ω ↦ X ω i * z ω) + E (fun ω ↦ X ω i * w ω)
    exact h2 i
  · intro c z
    have h1 : E (c • z) = c * E z := E.smul_eval c z
    have h2 : ∀ i, E (fun ω ↦ X ω i * (c • z) ω) = c * E (fun ω ↦ X ω i * z ω) := by
      intro i
      have hfun : (fun ω ↦ X ω i * (c • z) ω) = c • fun ω ↦ X ω i * z ω := by
        funext ω
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [hfun, E.smul_eval]
    show (E (c • z), fun i ↦ E (fun ω ↦ X ω i * (c • z) ω))
      = c • (E z, fun i ↦ E (fun ω ↦ X ω i * z ω))
    rw [Prod.smul_mk, Prod.mk.injEq]
    refine ⟨by rw [h1]; rfl, funext fun i ↦ ?_⟩
    show E (fun ω ↦ X ω i * (c • z) ω) = c * E (fun ω ↦ X ω i * z ω)
    exact h2 i

/-- A finitely supported expectation is continuous in the observable it integrates. This is
`FourthMomentMinimizer.continuous_of_repr` with an arbitrary parameter space. -/
theorem continuous_eval {α : Type*} [TopologicalSpace α] (E : ExpFunctional Ω) (p : Ω → ℝ)
    (hE : ∀ f : Ω → ℝ, E f = ∑ ω, p ω * f ω) (F : α → Ω → ℝ)
    (hF : ∀ ω, Continuous fun x ↦ F x ω) :
    Continuous fun x ↦ E (F x) := by
  have hfun : (fun x ↦ E (F x)) = fun x ↦ ∑ ω, p ω * F x ω := funext fun x ↦ hE (F x)
  rw [hfun]
  exact continuous_finset_sum _ fun ω _ ↦ continuous_const.mul (hF ω)

omit [Fintype ι] [DecidableEq ι] in
/-- The moment map is continuous for a finitely supported law. -/
theorem continuous_momentMap (E : ExpFunctional Ω) (p : Ω → ℝ)
    (hE : ∀ f : Ω → ℝ, E f = ∑ ω, p ω * f ω) (X : Ω → ι → ℝ) :
    Continuous (momentMap E X) := by
  have h1 : Continuous fun z : Ω → ℝ ↦ E z :=
    continuous_eval E p hE (fun z : Ω → ℝ ↦ z) fun ω ↦ continuous_apply ω
  have h2 : Continuous fun z : Ω → ℝ ↦ fun i ↦ E (fun ω ↦ X ω i * z ω) :=
    continuous_pi fun i ↦
      continuous_eval E p hE (fun (z : Ω → ℝ) ω ↦ X ω i * z ω)
        fun ω ↦ continuous_const.mul (continuous_apply ω)
  exact h1.prodMk h2

omit [Fintype ι] [DecidableEq ι] in
/-- **The zonoid is compact.** It is the continuous image of a cube. -/
theorem isCompact_scoreZonoid (E : ExpFunctional Ω) (p : Ω → ℝ)
    (hE : ∀ f : Ω → ℝ, E f = ∑ ω, p ω * f ω) (X : Ω → ι → ℝ) :
    IsCompact (scoreZonoid E X) :=
  (isCompact_univ_pi fun _ ↦ isCompact_Icc).image (continuous_momentMap E p hE X)

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
/-- **The zonoid is convex.** It is the linear image of a product of intervals. -/
theorem convex_scoreZonoid (E : ExpFunctional Ω) (X : Ω → ι → ℝ) :
    Convex ℝ (scoreZonoid E X) :=
  (convex_pi fun _ _ ↦ convex_Icc _ _).is_linear_image (momentMap_isLinear E X)

/-! ## Coordinates for a continuous linear functional -/

omit [Fintype Ω] in
/-- Every vector of `ℝ^p` is the sum of its coordinate spikes. -/
theorem single_decomposition (b : ι → ℝ) : b = ∑ i, Pi.single i (b i) := by
  funext j
  rw [Finset.sum_apply]
  simp [Pi.single_apply, Finset.sum_ite_eq]

omit [Fintype Ω] [Fintype ι] in
/-- A coordinate spike is a multiple of the unit spike. -/
theorem single_eq_smul (i : ι) (c : ℝ) :
    (Pi.single i c : ι → ℝ) = c • (Pi.single i (1 : ℝ) : ι → ℝ) := by
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

omit [Fintype Ω] in
/-- **Every continuous linear functional on `ℝ × ℝ^p` is an affine form in the manuscript's
coordinates `(λ₀, λ)`.** -/
theorem dual_representation (f : (ℝ × (ι → ℝ)) →L[ℝ] ℝ) (a : ℝ) (b : ι → ℝ) :
    f (a, b) = a * f (1, 0) + ∑ i, b i * f (0, Pi.single i (1 : ℝ)) := by
  have hadd : ∀ x y : ι → ℝ, f (0, x + y) = f (0, x) + f (0, y) := by
    intro x y
    have hp : ((0 : ℝ), x + y) = ((0 : ℝ), x) + ((0 : ℝ), y) := by
      rw [Prod.mk_add_mk, add_zero]
    rw [hp, map_add]
  have hsmul : ∀ (c : ℝ) (x : ι → ℝ), f (0, c • x) = c * f (0, x) := by
    intro c x
    have hp : ((0 : ℝ), c • x) = c • ((0 : ℝ), x) := by
      rw [Prod.smul_mk, smul_zero]
    rw [hp, map_smul, smul_eq_mul]
  have hzero : f ((0 : ℝ), (0 : ι → ℝ)) = 0 := by
    have hp : ((0 : ℝ), (0 : ι → ℝ)) = 0 := rfl
    rw [hp, map_zero]
  have hfin : ∀ s : Finset ι, f (0, ∑ i ∈ s, Pi.single i (b i))
      = ∑ i ∈ s, b i * f (0, Pi.single i (1 : ℝ)) := by
    intro s
    induction s using Finset.induction with
    | empty => simpa using hzero
    | @insert c s hc ih =>
        rw [Finset.sum_insert hc, Finset.sum_insert hc, hadd, ih,
          single_eq_smul c (b c), hsmul]
  have hsplit : (a, b) = (a, (0 : ι → ℝ)) + ((0 : ℝ), b) := by
    rw [Prod.mk_add_mk, add_zero, zero_add]
  have hfirst : f (a, (0 : ι → ℝ)) = a * f (1, 0) := by
    have hp : (a, (0 : ι → ℝ)) = a • ((1 : ℝ), (0 : ι → ℝ)) := by
      rw [Prod.smul_mk, smul_zero, smul_eq_mul, mul_one]
    rw [hp, map_smul, smul_eq_mul]
  rw [hsplit, map_add, hfirst]
  congr 1
  have hall := hfin Finset.univ
  rw [← single_decomposition b] at hall
  exact hall

/-! ## The converse of UPT (3.17) -/

/-- **UPT (3.17) implies membership in `𝒵_X`.** If every supporting-halfspace inequality
holds, the point cannot be separated from the compact convex zonoid, so it lies in it. -/
theorem mem_scoreZonoid_of_support (E : ExpFunctional Ω) (p : Ω → ℝ)
    (hE : ∀ f : Ω → ℝ, E f = ∑ ω, p ω * f ω) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ)
    (hsupp : ∀ (lam0 : ℝ) (lam : ι → ℝ),
      |lam0 * β + dot lam k| ≤ E (fun ω ↦ |lam0 + dot lam (X ω)|)) :
    (β, k) ∈ scoreZonoid E X := by
  by_contra hnot
  obtain ⟨f, u, hlt, hgt⟩ := geometric_hahn_banach_closed_point
    (convex_scoreZonoid E X) (isCompact_scoreZonoid E p hE X).isClosed hnot
  set lam0 : ℝ := f (1, 0) with hlam0
  set lam : ι → ℝ := fun i ↦ f (0, Pi.single i (1 : ℝ)) with hlam
  have hlamapp : ∀ i, lam i = f (0, Pi.single i (1 : ℝ)) := fun i ↦ rfl
  set zsign : Ω → ℝ := fun ω ↦ if 0 ≤ lam0 + dot lam (X ω) then (1 : ℝ) else -1
    with hzsign
  have hzapp : ∀ ω, zsign ω
      = if 0 ≤ lam0 + dot lam (X ω) then (1 : ℝ) else -1 := fun ω ↦ rfl
  have hzmem : zsign ∈ contractionBox Ω := by
    refine mem_contractionBox.mpr fun ω ↦ ?_
    rw [hzapp ω]
    by_cases h : 0 ≤ lam0 + dot lam (X ω) <;> simp [h]
  have hzval : ∀ ω, (lam0 + dot lam (X ω)) * zsign ω = |lam0 + dot lam (X ω)| := by
    intro ω
    rw [hzapp ω]
    by_cases h : 0 ≤ lam0 + dot lam (X ω)
    · rw [if_pos h, abs_of_nonneg h]
      ring
    · rw [if_neg h, abs_of_neg (not_le.mp h)]
      ring
  have hfz : f (momentMap E X zsign) = E (fun ω ↦ |lam0 + dot lam (X ω)|) := by
    rw [show momentMap E X zsign
        = (E zsign, fun i ↦ E (fun ω ↦ X ω i * zsign ω)) from rfl,
      dual_representation f (E zsign) (fun i ↦ E (fun ω ↦ X ω i * zsign ω))]
    have hlin := eval_affine_form E X zsign lam0 lam
    have hfun : (fun ω ↦ (lam0 + dot lam (X ω)) * zsign ω)
        = fun ω ↦ |lam0 + dot lam (X ω)| := funext hzval
    rw [hfun] at hlin
    rw [hlin]
    simp only [← hlam0, ← hlamapp]
    have hdot : dot lam (fun i ↦ E (fun ω ↦ X ω i * zsign ω))
        = ∑ i, E (fun ω ↦ X ω i * zsign ω) * lam i := by
      simp only [dot, Descent.Core.innerSum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hdot]
    ring
  have hft : f (β, k) = lam0 * β + dot lam k := by
    rw [dual_representation f β k]
    simp only [← hlam0, ← hlamapp]
    have hdot : dot lam k = ∑ i, k i * lam i := by
      simp only [dot, Descent.Core.innerSum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hdot]
    ring
  have h1 : f (momentMap E X zsign) < u := hlt _ ⟨zsign, hzmem, rfl⟩
  have h2 : u < f (β, k) := hgt
  have h3 := hsupp lam0 lam
  rw [hfz] at h1
  rw [hft] at h2
  have h4 : lam0 * β + dot lam k ≤ |lam0 * β + dot lam k| := le_abs_self _
  linarith

/-- **The converse of UPT (3.17), as the contraction it produces.** -/
theorem exists_contraction_of_support_bound (E : ExpFunctional Ω) (p : Ω → ℝ)
    (hE : ∀ f : Ω → ℝ, E f = ∑ ω, p ω * f ω) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ)
    (hsupp : ∀ (lam0 : ℝ) (lam : ι → ℝ),
      |lam0 * β + dot lam k| ≤ E (fun ω ↦ |lam0 + dot lam (X ω)|)) :
    ∃ z : Ω → ℝ, (∀ ω, |z ω| ≤ 1) ∧ E z = β ∧
      ∀ i, E (fun ω ↦ X ω i * z ω) = k i := by
  obtain ⟨z, hzmem, hzeq⟩ := mem_scoreZonoid_of_support E p hE X β k hsupp
  refine ⟨z, mem_contractionBox.mp hzmem, ?_, ?_⟩
  · exact congrArg Prod.fst hzeq
  · intro i
    exact congrFun (congrArg Prod.snd hzeq) i

/-- **UPT Theorem 3.2 in the direction (3.17) ⟹ `V = m²`.** The supporting-halfspace
inequalities produce a contraction, and the constant-second-moment pair built from it
attains `m²`, which `GlobalFourthMomentRegion.sq_le_minFourthMoment` shows is the floor. -/
theorem minFourthMoment_eq_sq_of_support (E : ExpFunctional Ω) (p : Ω → ℝ)
    (hE : ∀ f : Ω → ℝ, E f = ∑ ω, p ω * f ω) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ)
    (m : ℝ) (hm : 0 < m)
    (hsupp : ∀ (lam0 : ℝ) (lam : ι → ℝ), |lam0 * β + dot lam k|
      ≤ Real.sqrt m * E (fun ω ↦ |lam0 + dot lam (X ω)|)) :
    minFourthMoment E X β k m = m ^ 2 := by
  have hspos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hne : Real.sqrt m ≠ 0 := ne_of_gt hspos
  have hsm : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm.le
  have hscaled : ∀ (lam0 : ℝ) (lam : ι → ℝ),
      |lam0 * (β / Real.sqrt m) + dot lam (fun i ↦ k i / Real.sqrt m)|
        ≤ E (fun ω ↦ |lam0 + dot lam (X ω)|) := by
    intro lam0 lam
    have hdiv : ∀ i, k i / Real.sqrt m = (Real.sqrt m)⁻¹ * k i := by
      intro i
      rw [div_eq_inv_mul]
    have hfun : (fun i ↦ k i / Real.sqrt m) = fun i ↦ (Real.sqrt m)⁻¹ * k i := funext hdiv
    rw [hfun, dot_smul_right lam (Real.sqrt m)⁻¹ k]
    have hrw : lam0 * (β / Real.sqrt m) + (Real.sqrt m)⁻¹ * dot lam k
        = (lam0 * β + dot lam k) / Real.sqrt m := by
      field_simp
    rw [hrw, abs_div, abs_of_pos hspos, div_le_iff₀ hspos]
    have h := hsupp lam0 lam
    linarith
  obtain ⟨z, hz1, hz2, hz3⟩ :=
    exists_contraction_of_support_bound E p hE X (β / Real.sqrt m)
      (fun i ↦ k i / Real.sqrt m) hscaled
  have hzsq : ∀ ω, z ω ^ 2 ≤ 1 := by
    intro ω
    have h := hz1 ω
    nlinarith [abs_nonneg (z ω), sq_abs (z ω)]
  have hzb : Real.sqrt m * E z = β := by
    rw [hz2]
    field_simp
  have hzk : ∀ i, Real.sqrt m * E (fun ω ↦ X ω i * z ω) = k i := by
    intro i
    rw [hz3 i]
    field_simp
  exact (constant_magnitude_value E X β k m hm.le z hzsq hzb hzk).1

end

end Descent.Portability.ScoreMomentZonoid
