/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactMemoryLaw
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLin

assert_below Descent.Decision Descent.Program

/-!
Exact autonomous observables on a finite probability simplex. An arbitrary
possibly nonlinear update exists exactly when a linear update exists, provided
the observables retain total mass. This is the necessity direction of report
Theorem 14 as well as its familiar sufficient invariant-space condition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix

namespace Descent.Portability.ObservableClosureLaw

variable {S : Type*} [Fintype S] [Nonempty S]

/-- Every zero-mass signed direction is a positive multiple of a difference
of probability laws. No positivity assumption on that direction is required. -/
theorem zero_sum_probability_difference (direction : S → ℝ)
    (hzero : ∑ state, direction state = 0) :
    ∃ (first second : FiniteReportLaw S) (scale : ℝ),
      0 < scale ∧ direction = scale • (first.mass - second.mass) := by
  classical
  let scale : ℝ := Fintype.card S + ∑ state, |direction state|
  have hcard : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast Fintype.card_pos
  have habs : 0 ≤ ∑ state, |direction state| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hscale : 0 < scale := by dsimp [scale]; positivity
  let first : FiniteReportLaw S := {
    mass := fun state ↦ (1 + |direction state| + direction state) / scale
    mass_nonneg := fun state ↦ div_nonneg (by linarith [neg_abs_le (direction state)])
      (le_of_lt hscale)
    mass_sum := by
      rw [← Finset.sum_div]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, hzero, add_zero]
      exact div_self (ne_of_gt hscale) }
  let second : FiniteReportLaw S := {
    mass := fun state ↦ (1 + |direction state|) / scale
    mass_nonneg := fun state ↦ div_nonneg (by positivity) (le_of_lt hscale)
    mass_sum := by
      rw [← Finset.sum_div]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one]
      exact div_self (ne_of_gt hscale) }
  refine ⟨first, second, scale, hscale, ?_⟩
  funext state
  change direction state = scale *
    ((1 + |direction state| + direction state) / scale -
      (1 + |direction state|) / scale)
  field_simp
  ring

variable {E F V : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup V] [Module ℝ V]

/-- A linear target factors through linear observations exactly when their
kernel contains no target-visible direction. -/
theorem linear_factorization_iff (observe : V →ₗ[ℝ] E) (predict : V →ₗ[ℝ] F) :
    (∃ update : E →ₗ[ℝ] F, update.comp observe = predict) ↔
      LinearMap.ker observe ≤ LinearMap.ker predict := by
  constructor
  · rintro ⟨update, rfl⟩ direction hdirection
    simp only [LinearMap.mem_ker, LinearMap.comp_apply] at *
    rw [hdirection, map_zero]
  · intro hker
    let onRange : LinearMap.range observe →ₗ[ℝ] F :=
      ((LinearMap.ker observe).liftQ predict hker).comp
        observe.quotKerEquivRange.symm.toLinearMap
    obtain ⟨update, hupdate⟩ := onRange.exists_extend
    refine ⟨update, ?_⟩
    ext direction
    have heq := congrArg (fun linear : LinearMap.range observe →ₗ[ℝ] F ↦
      linear ⟨observe direction, ⟨direction, rfl⟩⟩) hupdate
    simpa [onRange, LinearMap.quotKerEquivRange_symm_apply_image] using heq

/-- Autonomy is stated without assuming the update is linear, continuous, or
known: equal observed expectations must imply equal predicted expectations. -/
def AutonomousOnLaws (observe : (S → ℝ) →ₗ[ℝ] E)
    (predict : (S → ℝ) →ₗ[ℝ] F) : Prop :=
  ∀ first second : FiniteReportLaw S,
    observe first.mass = observe second.mass → predict first.mass = predict second.mass

/-- Retaining total mass makes probability-law autonomy equivalent to exact
linear closure. Necessity tests genuine probability laws, not arbitrary signed rows. -/
theorem autonomy_iff_linear_update (observe : (S → ℝ) →ₗ[ℝ] E)
    (predict : (S → ℝ) →ₗ[ℝ] F)
    (hmass : ∀ direction, observe direction = 0 → ∑ state, direction state = 0) :
    AutonomousOnLaws observe predict ↔
      ∃ update : E →ₗ[ℝ] F, update.comp observe = predict := by
  rw [linear_factorization_iff]
  constructor
  · intro hautonomy direction hdirection
    have hobs : observe direction = 0 := hdirection
    obtain ⟨first, second, scale, hscale, heq⟩ :=
      zero_sum_probability_difference direction (hmass direction hobs)
    have hobseq : observe first.mass = observe second.mass := by
      rw [heq, map_smul, map_sub] at hobs
      have hz : observe first.mass - observe second.mass = 0 :=
        (smul_eq_zero.mp hobs).resolve_left (ne_of_gt hscale)
      exact sub_eq_zero.mp hz
    have hpred := hautonomy first second hobseq
    change predict direction = 0
    rw [heq, map_smul, map_sub, hpred, sub_self, smul_zero]
  · intro hker first second heq
    have hzero : observe (first.mass - second.mass) = 0 := by
      rw [map_sub, heq, sub_self]
    have hz := hker hzero
    change predict (first.mass - second.mass) = 0 at hz
    simpa only [map_sub, sub_eq_zero] using hz


variable {I : Type*} [Fintype I] [DecidableEq S] [DecidableEq I]

/-- The exact matrix criterion in report Theorem 14. The constant-one column
may be a linear combination of the reported features. The necessity holds even
if an autonomous updater was originally permitted to be nonlinear. -/
theorem matrix_autonomy_iff (transition : Matrix S S ℝ) (features : Matrix S I ℝ)
    (hconstant : ∃ coefficients : I → ℝ, features *ᵥ coefficients = fun _ ↦ 1) :
    AutonomousOnLaws features.transpose.toLin'
      ((transition * features).transpose.toLin') ↔
      ∃ update : Matrix I I ℝ, transition * features = features * update := by
  obtain ⟨coefficients, hconstant⟩ := hconstant
  have hmass (direction : S → ℝ) (hzero : features.transpose.toLin' direction = 0) :
      ∑ state, direction state = 0 := by
    have hweighted : ∑ feature, coefficients feature *
        (∑ state, features state feature * direction state) = 0 := by
      have heach (feature : I) : ∑ state, features state feature * direction state = 0 := by
        have hz := congrFun hzero feature
        simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct] using hz
      simp [heach]
    calc
      ∑ state, direction state =
          ∑ state, (∑ feature, features state feature * coefficients feature) *
            direction state := by
        apply Finset.sum_congr rfl
        intro state _
        have hc := congrFun hconstant state
        simp only [Matrix.mulVec, dotProduct] at hc
        rw [hc, one_mul]
      _ = ∑ feature, coefficients feature *
          (∑ state, features state feature * direction state) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro feature _
        apply Finset.sum_congr rfl
        intro state _
        ring
      _ = 0 := hweighted
  rw [autonomy_iff_linear_update _ _ hmass]
  constructor
  · rintro ⟨update, hupdate⟩
    refine ⟨(LinearMap.toMatrix' update).transpose, ?_⟩
    apply Matrix.transpose_injective
    apply Matrix.toLin'.injective
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.toLin'_mul,
      Matrix.toLin'_toMatrix'] using hupdate.symm
  · rintro ⟨update, hupdate⟩
    refine ⟨update.transpose.toLin', ?_⟩
    rw [hupdate, Matrix.transpose_mul, Matrix.toLin'_mul]

end Descent.Portability.ObservableClosureLaw
