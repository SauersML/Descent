/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.InfiniteGenomeLimit
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Operator.NormedSpace

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Feller semigroups of bounded jump generators

Theorem 9 of the research note "Ancestral locality" needs, on one finite window of the genome,
a forward semigroup whose generator is (7.1) with decisions. That generator is unbounded, so its
semigroup cannot be written as one exponential. The approximating models are pure jump processes
on the laws of the window: at a finite total rate the population jumps to a new law, and the
jump operator `J` averages an observable over the jump. This module builds the Feller semigroup
of such a model on any compact space `X`.

Positive operators. For a positive operator `J` on `C(X, ℝ)` that sends the constant one to
`rate • 1`, the sup norm grows by at most the rate, `‖J g‖ ≤ rate ‖g‖`
(`norm_apply_le_of_nonneg`). Its powers are positive (`pow_apply_nonneg`), and a norm-convergent
series of operators whose terms keep `g ≥ 0` nonnegative has a positive sum
(`nonneg_apply_of_hasSum`), so `exp(tJ)` is positive at every `t ≥ 0` (`exp_apply_nonneg`). A
generator `G` with `G 1 = 0` has `exp(tG) 1 = 1` (`exp_apply_one`).

The jump semigroup. `jumpOperator J rate t = exp(t (J - rate))`. Since `rate` is a scalar,
`exp(t (J - rate)) = exp(tJ) e^{-t rate}` (`jumpOperator_eq_mul`), so the operator is positive at
nonnegative times (`jumpOperator_nonneg`); it fixes the constants (`jumpOperator_one`), and
positivity with the unit gives the contraction (`norm_jumpOperator_apply_le`). The exponential law
gives the identity at time zero and the semigroup law (`jumpOperator_zero`, `jumpOperator_add`),
the derivative in time is the generator (`hasDerivAt_jumpOperator`), and the family is norm
continuous in time (`continuous_jumpOperator`). `jumpSemigroup` packages it as an
`InfiniteGenomeLimit.FellerSemigroup`, with operators `jumpOperator` (`jumpSemigroup_operator`).

Scope. Only bounded generators `J - rate` with `J` positive and `J 1 = rate • 1` are treated. The
forward generator (7.1) is not of this form, and no limit of jump semigroups is taken here.

## Empirical status

None. The bodies here are functional analysis of exponentials of bounded operators on continuous
functions of a compact space, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.AncestralLocality.JumpFellerSemigroup

open Filter Topology InfiniteGenomeLimit
open scoped NNReal

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The bounded operators on the continuous observables form a normed ring. -/
local instance instNormedRingOperator : NormedRing (C(X, ℝ) →L[ℝ] C(X, ℝ)) :=
  ContinuousLinearMap.toNormedRing

/-- The bounded operators on the continuous observables form a normed algebra. -/
local instance instNormedAlgebraOperator : NormedAlgebra ℝ (C(X, ℝ) →L[ℝ] C(X, ℝ)) :=
  ContinuousLinearMap.toNormedAlgebra

/-- The bounded operators on the continuous observables form a topological ring. -/
local instance instIsTopologicalRingOperator : IsTopologicalRing (C(X, ℝ) →L[ℝ] C(X, ℝ)) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

/-- Scalars commute with composition of operators. -/
local instance instSMulCommClassOperator :
    SMulCommClass ℝ (C(X, ℝ) →L[ℝ] C(X, ℝ)) (C(X, ℝ) →L[ℝ] C(X, ℝ)) :=
  Algebra.to_smulCommClass

/-- Scalars associate with composition of operators. -/
local instance instIsScalarTowerOperator :
    IsScalarTower ℝ (C(X, ℝ) →L[ℝ] C(X, ℝ)) (C(X, ℝ) →L[ℝ] C(X, ℝ)) :=
  IsScalarTower.right

/-! ## Positive operators -/

/-- The value at a point, as a bounded linear functional on continuous observables. -/
def evaluation (x : X) : C(X, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun g ↦ g x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl } 1 fun g ↦ by
    rw [one_mul]
    exact ContinuousMap.norm_coe_le_norm g x

/-- The value at a point of an observable. -/
theorem evaluation_apply (x : X) (g : C(X, ℝ)) : evaluation x g = g x :=
  rfl

/-- **A positive operator grows the sup norm by at most its rate.** If `J` is positive and sends
the constant one to `rate • 1`, then `‖J g‖ ≤ rate ‖g‖`: positivity applied to `‖g‖ • 1 ± g`
bounds `J g` pointwise by `rate ‖g‖`. -/
theorem norm_apply_le_of_nonneg (J : C(X, ℝ) →L[ℝ] C(X, ℝ)) {rate : ℝ} (hrate : 0 ≤ rate)
    (hpos : ∀ g, 0 ≤ g → 0 ≤ J g) (hone : J 1 = rate • 1) (g : C(X, ℝ)) :
    ‖J g‖ ≤ rate * ‖g‖ := by
  have hplus := hpos (‖g‖ • 1 + g) <| ContinuousMap.le_def.mpr fun x ↦ by
    have hx := ContinuousMap.neg_norm_le_apply g x
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
      ContinuousMap.zero_apply, smul_eq_mul, mul_one]
    linarith
  have hminus := hpos (‖g‖ • 1 - g) <| ContinuousMap.le_def.mpr fun x ↦ by
    have hx := ContinuousMap.apply_le_norm g x
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
      ContinuousMap.zero_apply, smul_eq_mul, mul_one]
    linarith
  refine (ContinuousMap.norm_le (J g) (mul_nonneg hrate (norm_nonneg g))).mpr fun x ↦ ?_
  have hp := ContinuousMap.le_def.mp hplus x
  have hm := ContinuousMap.le_def.mp hminus x
  simp only [map_add, map_sub, map_smul, hone, ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.smul_apply, ContinuousMap.one_apply, ContinuousMap.zero_apply, smul_eq_mul,
    mul_one] at hp hm
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- Powers of a positive operator are positive. -/
theorem pow_apply_nonneg {J : C(X, ℝ) →L[ℝ] C(X, ℝ)} (hpos : ∀ g, 0 ≤ g → 0 ≤ J g) (k : ℕ)
    {g : C(X, ℝ)} (hg : 0 ≤ g) : 0 ≤ (J ^ k) g := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    exact hpos _ ih

/-- **A convergent series of positive terms has a positive sum.** If a series of operators has
sum `A` and every term sends the nonnegative observable `g` to a nonnegative output, so does
`A`: evaluation at a point and at `g` is continuous and linear. -/
theorem nonneg_apply_of_hasSum {f : ℕ → C(X, ℝ) →L[ℝ] C(X, ℝ)} {A : C(X, ℝ) →L[ℝ] C(X, ℝ)}
    (hf : HasSum f A) {g : C(X, ℝ)} (hterm : ∀ k, 0 ≤ f k g) : 0 ≤ A g := by
  refine ContinuousMap.le_def.mpr fun x ↦ ?_
  have hx : HasSum (fun k ↦ f k g x) (A g x) :=
    ((evaluation x).comp (ContinuousLinearMap.apply ℝ C(X, ℝ) g)).hasSum hf
  rw [ContinuousMap.zero_apply]
  exact hasSum_le (fun k ↦ by simpa using ContinuousMap.le_def.mp (hterm k) x) hasSum_zero hx

/-- **The exponential of a positive operator is positive** at nonnegative times: every term
`t^k J^k / k!` of its series is. -/
theorem exp_apply_nonneg {J : C(X, ℝ) →L[ℝ] C(X, ℝ)} (hpos : ∀ g, 0 ≤ g → 0 ≤ J g) {t : ℝ}
    (ht : 0 ≤ t) {g : C(X, ℝ)} (hg : 0 ≤ g) : 0 ≤ NormedSpace.exp ℝ (t • J) g := by
  have hterm : ∀ k : ℕ, 0 ≤ ((k.factorial : ℝ)⁻¹ • (t • J) ^ k) g := by
    intro k
    rw [smul_pow, smul_smul, ContinuousLinearMap.smul_apply]
    refine ContinuousMap.le_def.mpr fun x ↦ ?_
    have hx := ContinuousMap.le_def.mp (pow_apply_nonneg hpos k hg) x
    rw [ContinuousMap.zero_apply] at hx ⊢
    rw [ContinuousMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_nonneg ht k)) hx
  exact nonneg_apply_of_hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • J)) hterm

/-- **A generator killing the constants fixes them.** If `G 1 = 0`, then `exp(tG) 1 = 1`: only
the zeroth term of the series survives. -/
theorem exp_apply_one {G : C(X, ℝ) →L[ℝ] C(X, ℝ)} (hG : G 1 = 0) (t : ℝ) :
    NormedSpace.exp ℝ (t • G) 1 = 1 := by
  have hsum : HasSum (fun k : ℕ ↦ ((k.factorial : ℝ)⁻¹ • (t • G) ^ k) 1)
      (NormedSpace.exp ℝ (t • G) 1) :=
    (ContinuousLinearMap.apply ℝ C(X, ℝ) (1 : C(X, ℝ))).hasSum
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • G))
  have hzero : ∀ k ≠ 0, ((k.factorial : ℝ)⁻¹ • (t • G) ^ k) 1 = 0 := by
    intro k hk
    cases k with
    | zero => exact absurd rfl hk
    | succ j =>
      rw [ContinuousLinearMap.smul_apply, pow_succ, ContinuousLinearMap.mul_apply,
        ContinuousLinearMap.smul_apply, hG, smul_zero, map_zero, smul_zero]
  have hsingle := hasSum_single 0 hzero
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    ContinuousLinearMap.one_apply] at hsingle
  exact hsum.unique hsingle

/-! ## The jump semigroup -/

/-- **The jump operator** at time `t`, `exp(t (J - rate))`. -/
def jumpOperator (J : C(X, ℝ) →L[ℝ] C(X, ℝ)) (rate t : ℝ) : C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  NormedSpace.exp ℝ (t • (J - rate • 1))

/-- **The jump generator kills the constants** when `J 1 = rate • 1`. -/
theorem jumpGenerator_one {J : C(X, ℝ) →L[ℝ] C(X, ℝ)} {rate : ℝ} (hone : J 1 = rate • 1) :
    (J - rate • 1) 1 = 0 := by
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, hone, sub_self]

/-- The jump operators fix the constants. -/
theorem jumpOperator_one {J : C(X, ℝ) →L[ℝ] C(X, ℝ)} {rate : ℝ} (hone : J 1 = rate • 1) (t : ℝ) :
    jumpOperator J rate t 1 = 1 :=
  exp_apply_one (jumpGenerator_one hone) t

/-- **The scalar part factors out**: `exp(t (J - rate)) = exp(tJ) e^{-t rate}`. -/
theorem jumpOperator_eq_mul (J : C(X, ℝ) →L[ℝ] C(X, ℝ)) (rate t : ℝ) :
    jumpOperator J rate t = NormedSpace.exp ℝ (t • J) *
      algebraMap ℝ (C(X, ℝ) →L[ℝ] C(X, ℝ)) (Real.exp (-(t * rate))) := by
  have hscalar : NormedSpace.exp ℝ (algebraMap ℝ (C(X, ℝ) →L[ℝ] C(X, ℝ)) (-(t * rate))) =
      algebraMap ℝ (C(X, ℝ) →L[ℝ] C(X, ℝ)) (Real.exp (-(t * rate))) := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (-(t * rate))).symm
  have hdecomp : t • (J - rate • 1) =
      t • J + algebraMap ℝ (C(X, ℝ) →L[ℝ] C(X, ℝ)) (-(t * rate)) := by
    rw [Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul, neg_smul, sub_eq_add_neg]
  rw [jumpOperator, hdecomp, NormedSpace.exp_add_of_commute
    (Algebra.commutes (-(t * rate)) (t • J)).symm, hscalar]

/-- **The jump operators are positive** at nonnegative times. -/
theorem jumpOperator_nonneg {J : C(X, ℝ) →L[ℝ] C(X, ℝ)} (hpos : ∀ g, 0 ≤ g → 0 ≤ J g)
    (rate : ℝ) {t : ℝ} (ht : 0 ≤ t) {g : C(X, ℝ)} (hg : 0 ≤ g) : 0 ≤ jumpOperator J rate t g := by
  have hscale : 0 ≤ Real.exp (-(t * rate)) • g := ContinuousMap.le_def.mpr fun x ↦ by
    have hx := ContinuousMap.le_def.mp hg x
    rw [ContinuousMap.zero_apply] at hx ⊢
    rw [ContinuousMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (Real.exp_pos _).le hx
  have hsplit : jumpOperator J rate t g =
      NormedSpace.exp ℝ (t • J) (Real.exp (-(t * rate)) • g) := by
    rw [jumpOperator_eq_mul, ContinuousLinearMap.mul_apply, Algebra.algebraMap_eq_smul_one,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  rw [hsplit]
  exact exp_apply_nonneg hpos ht hscale

/-- **The jump operators contract the sup norm** at nonnegative times: they are positive and fix
the constants. -/
theorem norm_jumpOperator_apply_le {J : C(X, ℝ) →L[ℝ] C(X, ℝ)} (hpos : ∀ g, 0 ≤ g → 0 ≤ J g)
    {rate : ℝ} (hone : J 1 = rate • 1) {t : ℝ} (ht : 0 ≤ t) (g : C(X, ℝ)) :
    ‖jumpOperator J rate t g‖ ≤ ‖g‖ := by
  have hunit : jumpOperator J rate t 1 = (1 : ℝ) • 1 := by
    rw [one_smul]
    exact jumpOperator_one hone t
  have h := norm_apply_le_of_nonneg (jumpOperator J rate t) zero_le_one
    (fun _ hg ↦ jumpOperator_nonneg hpos rate ht hg) hunit g
  rwa [one_mul] at h

/-- At time zero the jump operator is the identity. -/
theorem jumpOperator_zero (J : C(X, ℝ) →L[ℝ] C(X, ℝ)) (rate : ℝ) :
    jumpOperator J rate 0 = ContinuousLinearMap.id ℝ C(X, ℝ) :=
  calc jumpOperator J rate 0 = 1 := by rw [jumpOperator, zero_smul, NormedSpace.exp_zero]
    _ = ContinuousLinearMap.id ℝ C(X, ℝ) := rfl

/-- **The semigroup law** of the jump operators, at all real times. -/
theorem jumpOperator_add (J : C(X, ℝ) →L[ℝ] C(X, ℝ)) (rate s t : ℝ) :
    jumpOperator J rate (s + t) = jumpOperator J rate s * jumpOperator J rate t := by
  have hcomm : Commute (s • (J - rate • 1)) (t • (J - rate • 1)) := by
    show s • (J - rate • 1) * t • (J - rate • 1) = t • (J - rate • 1) * s • (J - rate • 1)
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm s t]
  rw [jumpOperator, jumpOperator, jumpOperator, add_smul, NormedSpace.exp_add_of_commute hcomm]

/-- **The derivative in time is the generator**,
`d/dt exp(t (J - rate)) = (J - rate) exp(t (J - rate))`. -/
theorem hasDerivAt_jumpOperator (J : C(X, ℝ) →L[ℝ] C(X, ℝ)) (rate t : ℝ) :
    HasDerivAt (jumpOperator J rate) ((J - rate • 1) * jumpOperator J rate t) t := by
  unfold jumpOperator
  exact hasDerivAt_exp_smul_const' (J - rate • 1) t

/-- The jump operators are continuous in time in the operator norm. -/
theorem continuous_jumpOperator (J : C(X, ℝ) →L[ℝ] C(X, ℝ)) (rate : ℝ) :
    Continuous (jumpOperator J rate) :=
  continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_jumpOperator J rate t).continuousAt

/-- **The jump semigroup** of a positive operator `J` with `J 1 = rate • 1`: the operators
`exp(t (J - rate))` at nonnegative times form a Feller semigroup. -/
def jumpSemigroup (J : C(X, ℝ) →L[ℝ] C(X, ℝ)) (rate : ℝ) (hpos : ∀ g, 0 ≤ g → 0 ≤ J g)
    (hone : J 1 = rate • 1) : FellerSemigroup X where
  operator t := jumpOperator J rate t
  norm_le t g := norm_jumpOperator_apply_le hpos hone (NNReal.coe_nonneg t) g
  map_one t := jumpOperator_one hone t
  nonneg t _ hg := jumpOperator_nonneg hpos rate (NNReal.coe_nonneg t) hg
  operator_zero := by
    rw [NNReal.coe_zero]
    exact jumpOperator_zero J rate
  operator_add s t := by
    rw [NNReal.coe_add]
    exact jumpOperator_add J rate s t
  tendsto_operator_zero g := by
    have hcont : Continuous fun t : ℝ≥0 ↦ jumpOperator J rate t g :=
      ((ContinuousLinearMap.apply ℝ C(X, ℝ) g).continuous.comp
        (continuous_jumpOperator J rate)).comp NNReal.continuous_coe
    have h := hcont.tendsto 0
    simpa only [NNReal.coe_zero, jumpOperator_zero, ContinuousLinearMap.id_apply] using h

/-- The operators of the jump semigroup are the jump operators. -/
theorem jumpSemigroup_operator (J : C(X, ℝ) →L[ℝ] C(X, ℝ)) (rate : ℝ)
    (hpos : ∀ g, 0 ≤ g → 0 ≤ J g) (hone : J 1 = rate • 1) (t : ℝ≥0) :
    (jumpSemigroup J rate hpos hone).operator t = jumpOperator J rate t :=
  rfl

end

end Descent.Pangenome.AncestralLocality.JumpFellerSemigroup
