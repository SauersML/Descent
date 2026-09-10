/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncientPrediction.Correction
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

assert_below Descent.Decision Descent.Program

/-!
# Least-favorable population mixtures

The inverse quadratic objective and its first-order condition. Covariances
are represented as self-adjoint operators, so the development is independent
of the choice of basis for the correction dictionary.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncientPrediction

open scoped BigOperators RealInnerProductSpace
open Filter Topology

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Solve the normal equation using the inverse in the operator algebra. -/
noncomputable def normalSolution (u : E) (V : E →L[ℝ] E) : E := Ring.inverse V u

/-- The mixture value `uᵀ V⁻¹ u`. Theorems below require invertibility. -/
noncomputable def inverseQuadratic (u : E) (V : E →L[ℝ] E) : ℝ :=
  ⟪u, normalSolution u V⟫

omit [CompleteSpace E] in
lemma normalSolution_equation (u : E) (V : E →L[ℝ] E) (hV : IsUnit V) :
    V (normalSolution u V) = u := by
  have := congrArg (fun f : E →L[ℝ] E => f u) (Ring.mul_inverse_cancel V hV)
  simpa [normalSolution, ContinuousLinearMap.mul_apply] using this

/-- Differentiating the normal equation avoids imposing a formula for the
optimizer's derivative as an assumption. -/
theorem inverseQuadratic_fderiv (U : F →L[ℝ] E) (M : F →L[ℝ] E →L[ℝ] E)
    (x : F) (hunit : IsUnit (M x))
    (hsym : ∀ a b, ⟪a, M x b⟫ = ⟪M x a, b⟫) :
    DifferentiableAt ℝ (fun y => inverseQuadratic (U y) (M y)) x ∧
    ∀ d, fderiv ℝ (fun y => inverseQuadratic (U y) (M y)) x d =
      2 * ⟪U d, normalSolution (U x) (M x)⟫ -
      ⟪normalSolution (U x) (M x), M d (normalSolution (U x) (M x))⟫ := by
  let a : F → E := fun y => normalSolution (U y) (M y)
  have ha : DifferentiableAt ℝ a x :=
    ((differentiableAt_inverse hunit).comp x M.differentiableAt).clm_apply U.differentiableAt
  have hnear : (fun y => M y (a y)) =ᶠ[𝓝 x] U := by
    have hu : ∀ᶠ y in 𝓝 x, IsUnit (M y) :=
      M.continuous.continuousAt (Units.isOpen.mem_nhds hunit)
    filter_upwards [hu] with y hy
    exact normalSolution_equation (U y) (M y) hy
  have hnormal := (M.hasFDerivAt.clm_apply ha.hasFDerivAt).congr_of_eventuallyEq hnear.symm
  have hD : (M x).comp (fderiv ℝ a x) + M.flip (a x) = U :=
    hnormal.unique U.hasFDerivAt
  have hq := U.hasFDerivAt.inner ℝ ha.hasFDerivAt
  refine ⟨hq.differentiableAt, fun d => ?_⟩
  have heq : M x (fderiv ℝ a x d) + M d (a x) = U d :=
    congrArg (fun f : F →L[ℝ] E => f d) hD
  have hinner := congrArg (fun z => ⟪a x, z⟫) heq
  dsimp only at hinner
  have hstationary : M x (a x) = U x := normalSolution_equation (U x) (M x) hunit
  rw [inner_add_right, hsym, hstationary] at hinner
  change fderiv ℝ (fun y => ⟪U y, a y⟫) x d = _
  rw [hq.fderiv]
  change ⟪U x, fderiv ℝ a x d⟫ + ⟪U d, a x⟫ = _
  rw [real_inner_comm (a x) (U d)] at hinner
  dsimp [a] at *
  linarith

/-- Continuous linear averaging of a finite family by population weights. -/
noncomputable def mixtureMap [Fintype G] (v : G → F) : (G → ℝ) →L[ℝ] F :=
  ∑ g, (ContinuousLinearMap.proj g).smulRight (v g)

@[simp] lemma mixtureMap_apply [Fintype G] (v : G → F) (w : G → ℝ) :
    mixtureMap v w = ∑ g, w g • v g := by
  simp [mixtureMap]

section FiniteMixtures

variable [Fintype G] [Nonempty G] [FiniteDimensional ℝ E]

/-- A positive definite feature second moment as an operator. -/
structure PositiveMoment (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  op : E →L[ℝ] E
  symmetric : ∀ x y, ⟪x, op y⟫ = ⟪op x, y⟫
  positive : ∀ x, x ≠ 0 → 0 < ⟪x, op x⟫

lemma PositiveMoment.nonneg (V : PositiveMoment E) (x : E) : 0 ≤ ⟪x, V.op x⟫ := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (V.positive x hx).le

/-- Each population's improvement, with different second moments permitted. -/
def populationGain (u : E) (V : PositiveMoment E) (a : E) : ℝ :=
  2 * ⟪u, a⟫ - ⟪a, V.op a⟫

lemma simplex_positive_weight (w : G → ℝ) (hw : w ∈ stdSimplex ℝ G) :
    ∃ g, 0 < w g := by
  by_contra h
  push_neg at h
  have hz : ∀ g, w g = 0 := fun g => le_antisymm (h g) (hw.1 g)
  have := hw.2
  simp [hz] at this

lemma mixture_symmetric (V : G → PositiveMoment E) (w : G → ℝ) (x y : E) :
    ⟪x, mixtureMap (fun g => (V g).op) w y⟫ =
      ⟪mixtureMap (fun g => (V g).op) w x, y⟫ := by
  simp only [mixtureMap_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, inner_sum, sum_inner,
    inner_smul_right, real_inner_smul_left]
  apply Finset.sum_congr rfl
  intro g _
  rw [(V g).symmetric]

lemma mixture_positive (V : G → PositiveMoment E) (w : G → ℝ)
    (hw : w ∈ stdSimplex ℝ G) (x : E) (hx : x ≠ 0) :
    0 < ⟪x, mixtureMap (fun g => (V g).op) w x⟫ := by
  simp only [mixtureMap_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, inner_sum, inner_smul_right]
  obtain ⟨g, hg⟩ := simplex_positive_weight w hw
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hw.1 i) ((V i).nonneg x))
    ⟨g, Finset.mem_univ g, mul_pos hg ((V g).positive x hx)⟩

lemma mixture_isUnit (V : G → PositiveMoment E) (w : G → ℝ)
    (hw : w ∈ stdSimplex ℝ G) : IsUnit (mixtureMap (fun g => (V g).op) w) := by
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  have hinj : Function.Injective (mixtureMap (fun g => (V g).op) w) := by
    intro a b hab
    by_contra hne
    have hpos := mixture_positive V w hw (a - b) (sub_ne_zero.mpr hne)
    have hz : mixtureMap (fun g => (V g).op) w (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    simp [hz] at hpos
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

lemma mixed_gain (u : G → E) (V : G → PositiveMoment E) (w : G → ℝ) (a : E) :
    (∑ g, w g * populationGain (u g) (V g) a) =
      2 * ⟪mixtureMap u w, a⟫ - ⟪a, mixtureMap (fun g => (V g).op) w a⟫ := by
  simp only [populationGain, mixtureMap_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, inner_sum, sum_inner,
    inner_smul_right, real_inner_smul_left, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  ring

/-- Completing the square proves the dual upper bound for every update. -/
lemma mixture_upper_bound (u : G → E) (V : G → PositiveMoment E) (w : G → ℝ)
    (hw : w ∈ stdSimplex ℝ G) (a : E) :
    (∑ g, w g * populationGain (u g) (V g) a) ≤
      inverseQuadratic (mixtureMap u w) (mixtureMap (fun g => (V g).op) w) := by
  let M := mixtureMap (fun g => (V g).op) w
  let b := normalSolution (mixtureMap u w) M
  have hn : M b = mixtureMap u w := normalSolution_equation _ _ (mixture_isUnit V w hw)
  have hpos : 0 ≤ ⟪a - b, M (a - b)⟫ := by
    by_cases he : a - b = 0
    · simp [he]
    · exact (mixture_positive V w hw _ he).le
  rw [mixed_gain]
  change 2 * ⟪mixtureMap u w, a⟫ - ⟪a, M a⟫ ≤ ⟪mixtureMap u w, b⟫
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hn,
    mixture_symmetric V w b a, hn] at hpos
  rw [real_inner_comm a (mixtureMap u w), real_inner_comm b (mixtureMap u w)] at hpos
  linarith

@[simp] lemma mixtureMap_single (v : G → F) (g : G) [DecidableEq G] :
    mixtureMap v (Pi.single g 1) = v g := by
  simp [mixtureMap_apply, Pi.single_apply, ite_smul]

/-- Theorem 7: a least-favorable mixture exists, its normal-equation solution
attains the largest uniform population gain, and its inverse quadratic value
is the minimum over all mixtures. `IsGreatest` includes attainment. -/
theorem least_favorable_mixture (u : G → E) (V : G → PositiveMoment E) :
    ∃ w ∈ stdSimplex ℝ G,
      IsLeast ((fun z => inverseQuadratic (mixtureMap u z)
        (mixtureMap (fun g => (V g).op) z)) '' stdSimplex ℝ G)
        (inverseQuadratic (mixtureMap u w) (mixtureMap (fun g => (V g).op) w)) ∧
      IsGreatest {t : ℝ | ∃ a : E, ∀ g, t ≤ populationGain (u g) (V g) a}
        (inverseQuadratic (mixtureMap u w) (mixtureMap (fun g => (V g).op) w)) ∧
      ∀ g, inverseQuadratic (mixtureMap u w) (mixtureMap (fun g => (V g).op) w) ≤
        populationGain (u g) (V g)
          (normalSolution (mixtureMap u w) (mixtureMap (fun g => (V g).op) w)) := by
  classical
  let U := mixtureMap u
  let M := mixtureMap (fun g => (V g).op)
  let q := fun z => inverseQuadratic (U z) (M z)
  have hd (w : G → ℝ) (hw : w ∈ stdSimplex ℝ G) :=
    inverseQuadratic_fderiv U M w (mixture_isUnit V w hw) (mixture_symmetric V w)
  have hc : ContinuousOn q (stdSimplex ℝ G) := fun w hw =>
    (hd w hw).1.continuousAt.continuousWithinAt
  obtain ⟨w, hw, hmin⟩ := (isCompact_stdSimplex G).exists_isMinOn
    ⟨Pi.single (Classical.arbitrary G) 1, single_mem_stdSimplex ℝ _⟩ hc
  let a := normalSolution (U w) (M w)
  have hn : M w a = U w := normalSolution_equation _ _ (mixture_isUnit V w hw)
  have hgain : ∀ g, q w ≤ populationGain (u g) (V g) a := by
    intro g
    have hvertex := single_mem_stdSimplex ℝ g
    have ht := sub_mem_posTangentConeAt_of_segment_subset
      ((convex_stdSimplex ℝ G).segment_subset hw hvertex)
    have hder := hmin.localize.hasFDerivWithinAt_nonneg
      (hd w hw).1.hasFDerivAt.hasFDerivWithinAt ht
    rw [(hd w hw).2] at hder
    change 0 ≤ 2 * ⟪U (Pi.single g 1 - w), a⟫ - ⟪a, M (Pi.single g 1 - w) a⟫ at hder
    simp only [map_sub, U, M, mixtureMap_single, ContinuousLinearMap.sub_apply] at hder
    change 0 ≤ 2 * ⟪u g - U w, a⟫ - ⟪a, (V g).op a - M w a⟫ at hder
    rw [inner_sub_left, inner_sub_right, hn, real_inner_comm a (U w)] at hder
    change ⟪U w, a⟫ ≤ 2 * ⟪u g, a⟫ - ⟪a, (V g).op a⟫
    linarith
  refine ⟨w, hw, ⟨⟨w, hw, rfl⟩, ?_⟩, ⟨⟨a, hgain⟩, ?_⟩, hgain⟩
  · rintro t ⟨z, hz, rfl⟩
    exact hmin hz
  · rintro t ⟨b, hb⟩
    have hle : t ≤ ∑ g, w g * populationGain (u g) (V g) b := by
      calc
        t = ∑ g, w g * t := by rw [← Finset.sum_mul, hw.2, one_mul]
        _ ≤ _ := Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_left (hb g) (hw.1 g)
    exact hle.trans (mixture_upper_bound u V w hw b)

end FiniteMixtures

end Descent.Portability.AncientPrediction
