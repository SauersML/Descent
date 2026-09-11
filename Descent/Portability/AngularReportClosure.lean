/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CohortEvaluationOperators

assert_below Descent.Decision Descent.Program

/-!
# Exact finite-dimensional angular closure of the cohort reports

PL Theorem 6.2 says that one nonlinear second-moment matrix determines the expected
explainability of every fixed projection report.  This module proves it.  The conditional
angular matrix `Γ_V = E[V Vᵀ / VᵀV]` of PL (6.4) is `angularMatrix`, defined entrywise from an
`ExpFunctional`; `angularMatrix_trace` and `angularMatrix_posSemidef` prove that it is positive
semidefinite with trace one without any raw-moment assumption, exactly as the manuscript claims.
The boxed identity PL (6.5), `E[VᵀBV / VᵀV] = tr(B Γ_V)`, is `angular_report_identity`; it needs
no hypothesis at all, not even symmetry of `B`, and not even that the law avoids the degenerate
set.  PL (6.6) then follows for both cohort reports of
`Descent.Portability.CohortEvaluationOperators`: `expected_partialR2_eq_trace` computes the
expected group report as `tr(Π_z Γ_r)` and `expected_loss_report_eq_trace` the expected
loss-regression report as `tr(J_H Γ_{z_L})`.  Equality of expected rank-one projection reports
in every direction is equivalent to equality of the angular matrices
(`angularMatrix_eq_iff_expected_reports_eq`), by the quadratic-form extensionality of that
module.

PL Proposition 6.4 is the projective state.  The projection `P(y) = y yᵀ / yᵀy` of PL (6.10) is
literally the rank-one angular projection already defined for the residual score direction, so
it is reused rather than redefined.  `rankOneProj_eq_iff` proves that two nonzero vectors have
the same projective state exactly when they differ by a nonzero scalar,
`scale_invariant_report_factors` builds the factoring map for every scale-invariant report, and
`invariant_reports_eq_iff_projective_eq` proves that two laws agree on every
scale-invariant report exactly when they agree on every function of the projective state.
`outer_eq_radius_smul_projState` is the manuscript's remark that retaining `‖y‖²` recovers every
homogeneous quadratic error, and `fixed_prediction_loss_not_scale_invariant` exhibits the
concrete failure of the fixed-prediction loss `‖y - s‖²` to be covered by that representation.

The "conditional on `V ≠ 0`" of PL (6.4) is the hypothesis `∀ ω, V ω ≠ 0`: the law puts no mass
on the degenerate set, which is a domain condition on the law and not an assumption about the
reports.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AngularReportClosure

open Foundations Matrix CohortEvaluationOperators

noncomputable section

variable {Ω : Type*} {d n : ℕ}

/-! ## The inner sum vanishes only at the zero vector -/

/-- A real vector has zero squared length exactly when it is the zero vector. -/
theorem dot_self_eq_zero {v : Fin d → ℝ} : dot v v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have hsum : ∑ j, v j * v j = 0 := h
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ ↦ mul_self_nonneg (v j))).mp hsum i (Finset.mem_univ i)
    simpa using mul_self_eq_zero.mp hi
  · intro h
    rw [h]
    simp [dot, Descent.Core.innerSum]

/-- A nonzero vector has nonzero squared length. -/
theorem dot_self_ne_zero {v : Fin d → ℝ} (hv : v ≠ 0) : dot v v ≠ 0 := fun h ↦
  hv (dot_self_eq_zero.mp h)

/-! ## The conditional angular matrix -/

/-- **PL (6.4).**  The conditional angular matrix `Γ_V = E[V Vᵀ / VᵀV]` of a vector-valued
observable, defined entrywise from a normalized linear expectation.  Each entry is the
expectation of a bounded observable, so no raw-moment assumption is needed. -/
def angularMatrix (E : ExpFunctional Ω) (V : Ω → Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j ↦ E (fun ω ↦ V ω i * V ω j / dot (V ω) (V ω))

/-- The angular matrix is symmetric. -/
theorem angularMatrix_transpose (E : ExpFunctional Ω) (V : Ω → Fin d → ℝ) :
    (angularMatrix E V)ᵀ = angularMatrix E V := by
  ext i j
  simp only [Matrix.transpose_apply, angularMatrix, Matrix.of_apply]
  exact congrArg E.eval (funext fun ω ↦ by ring)

/-- The angular matrix is Hermitian, which over the reals is symmetry. -/
theorem angularMatrix_isHermitian (E : ExpFunctional Ω) (V : Ω → Fin d → ℝ) :
    Matrix.IsHermitian (angularMatrix E V) := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact angularMatrix_transpose E V

/-- A quadratic form is the trace of the outer product against the matrix.  Symmetry of the
matrix is not needed: relabelling the two summation indices supplies it. -/
theorem quadForm_eq_trace_outer (B : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) :
    quadForm B w = Matrix.trace (Matrix.vecMulVec w w * B) := by
  simp only [quadForm, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.vecMulVec_apply, dot, Descent.Core.innerSum, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- Applying an outer product to a vector. -/
theorem vecMulVec_mulVec (x y v : Fin d → ℝ) :
    (Matrix.vecMulVec x y).mulVec v = (dot y v) • x := by
  funext i
  have hl : (Matrix.vecMulVec x y).mulVec v i = ∑ j, x i * y j * v j := by
    simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply]
  have hr : ((dot y v) • x) i = ∑ j, x i * y j * v j := by
    simp only [Pi.smul_apply, smul_eq_mul, dot, Descent.Core.innerSum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [hl, hr]

/-- The quadratic form of an outer product is the squared inner sum. -/
theorem quadForm_vecMulVec (w v : Fin d → ℝ) :
    quadForm (Matrix.vecMulVec w w) v = (dot w v) ^ 2 := by
  rw [quadForm, vecMulVec_mulVec, dot_smul_right, dot_comm v w]
  ring

/-- **PL (6.5), the exact angular closure identity.**  For every fixed matrix `B`, the expected
normalized quadratic form of `V` is the trace pairing of `B` with the angular matrix.  No
hypothesis is needed: the manuscript states it for symmetric `B`, but relabelling the summation
indices shows that symmetry is never used, and the identity is insensitive to how the degenerate
set is scored because both sides score it by the same convention. -/
theorem angular_report_identity (E : ExpFunctional Ω) (V : Ω → Fin d → ℝ)
    (B : Matrix (Fin d) (Fin d) ℝ) :
    E (fun ω ↦ quadForm B (V ω) / dot (V ω) (V ω))
      = Matrix.trace (B * angularMatrix E V) := by
  have hpoint : ∀ ω : Ω, quadForm B (V ω) / dot (V ω) (V ω)
      = ∑ i, ∑ j, B i j * (V ω j * V ω i / dot (V ω) (V ω)) := by
    intro ω
    have h1 : quadForm B (V ω) = ∑ i, ∑ j, V ω i * (B i j * V ω j) := by
      simp [quadForm, dot, Descent.Core.innerSum, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [h1, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hfun : (fun ω ↦ quadForm B (V ω) / dot (V ω) (V ω))
      = ∑ i : Fin d, ∑ j : Fin d,
          (B i j) • (fun ω ↦ V ω j * V ω i / dot (V ω) (V ω)) := by
    funext ω
    rw [hpoint ω]
    simp [Finset.sum_apply]
  have hinner : ∀ i : Fin d,
      E (∑ j : Fin d, (B i j) • (fun ω ↦ V ω j * V ω i / dot (V ω) (V ω)))
        = ∑ j : Fin d, B i j * E (fun ω ↦ V ω j * V ω i / dot (V ω) (V ω)) := by
    intro i
    rw [ExpFunctional.eval_sum]
    exact Finset.sum_congr rfl fun j _ ↦ E.smul_eval _ _
  rw [hfun, ExpFunctional.eval_sum]
  simp only [hinner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, angularMatrix,
    Matrix.of_apply]

/-- **The angular matrix has trace one.**  The hypothesis is the manuscript's conditioning: the
law puts no mass on the degenerate set `V = 0`. -/
theorem angularMatrix_trace (E : ExpFunctional Ω) (V : Ω → Fin d → ℝ) (hV : ∀ ω, V ω ≠ 0) :
    Matrix.trace (angularMatrix E V) = 1 := by
  have hfun : Finset.sum Finset.univ
      (fun i : Fin d ↦ fun ω ↦ V ω i * V ω i / dot (V ω) (V ω)) = fun _ : Ω ↦ (1 : ℝ) := by
    funext ω
    rw [Finset.sum_apply, ← Finset.sum_div]
    have hnum : (∑ i, V ω i * V ω i) = dot (V ω) (V ω) := rfl
    rw [hnum]
    exact div_self (dot_self_ne_zero (hV ω))
  simp only [Matrix.trace, Matrix.diag_apply, angularMatrix, Matrix.of_apply]
  rw [← ExpFunctional.eval_sum, hfun, ExpFunctional.eval_const]

/-- The quadratic form of the angular matrix is the expected normalized squared inner sum. -/
theorem quadForm_angularMatrix (E : ExpFunctional Ω) (V : Ω → Fin d → ℝ) (w : Fin d → ℝ) :
    quadForm (angularMatrix E V) w
      = E (fun ω ↦ (dot w (V ω)) ^ 2 / dot (V ω) (V ω)) := by
  rw [quadForm_eq_trace_outer, ← angular_report_identity E V (Matrix.vecMulVec w w)]
  exact congrArg E.eval (funext fun ω ↦ by rw [quadForm_vecMulVec])

/-- The angular matrix is positive semidefinite. -/
theorem quadForm_angularMatrix_nonneg (E : ExpFunctional Ω) (V : Ω → Fin d → ℝ)
    (w : Fin d → ℝ) : 0 ≤ quadForm (angularMatrix E V) w := by
  rw [quadForm_angularMatrix]
  exact E.nonneg_eval _ fun ω ↦ div_nonneg (sq_nonneg _) (dot_self_nonneg _)

/-- **The angular matrix is positive semidefinite**, in the Mathlib sense, with no raw-moment
assumption: a normalized outer product is positive semidefinite with trace one, so its entries
are bounded and its expectation exists. -/
theorem angularMatrix_posSemidef (E : ExpFunctional Ω) (V : Ω → Fin d → ℝ) :
    Matrix.PosSemidef (angularMatrix E V) := by
  refine ⟨angularMatrix_isHermitian E V, fun x ↦ ?_⟩
  have hx : star x ⬝ᵥ (angularMatrix E V).mulVec x = quadForm (angularMatrix E V) x := rfl
  rw [hx]
  exact quadForm_angularMatrix_nonneg E V x

/-- **Equal expected projection reports in every direction means equal angular matrices.**  This
is the identifiability half of PL Theorem 6.2, and it is the quadratic-form extensionality of
`Descent.Portability.CohortEvaluationOperators` applied to two symmetric matrices. -/
theorem angularMatrix_eq_iff_expected_reports_eq {Ω₁ Ω₂ : Type*} (E₁ : ExpFunctional Ω₁)
    (E₂ : ExpFunctional Ω₂) (V₁ : Ω₁ → Fin d → ℝ) (V₂ : Ω₂ → Fin d → ℝ) :
    (∀ w : Fin d → ℝ, E₁ (fun ω ↦ (dot w (V₁ ω)) ^ 2 / dot (V₁ ω) (V₁ ω))
        = E₂ (fun ω ↦ (dot w (V₂ ω)) ^ 2 / dot (V₂ ω) (V₂ ω)))
      ↔ angularMatrix E₁ V₁ = angularMatrix E₂ V₂ := by
  constructor
  · intro h
    refine (quadForm_ext_iff _ _ (angularMatrix_transpose E₁ V₁)
      (angularMatrix_transpose E₂ V₂)).mp fun w ↦ ?_
    rw [quadForm_angularMatrix, quadForm_angularMatrix]
    exact h w
  · intro h w
    rw [← quadForm_angularMatrix, ← quadForm_angularMatrix, h]

/-! ## PL (6.6): both cohort reports are angular -/

/-- **PL (6.6), the group report.**  The expected partial squared correlation of the cohort
against a fixed residual score direction is the trace pairing of the rank-one angular projection
with the angular matrix of the residual outcome vector.  Under the manuscript's conditioning
`r ≠ 0`, that is `∀ ω, R ω ≠ 0`, every value entering the left-hand expectation is an actual
report; the identity itself needs no hypothesis. -/
theorem expected_partialR2_eq_trace (E : ExpFunctional Ω) (R : Ω → Fin d → ℝ)
    (z : Fin d → ℝ) :
    E (fun ω ↦ partialR2 z (R ω))
      = Matrix.trace (rankOneProj z * angularMatrix E R) := by
  rw [← angular_report_identity E R (rankOneProj z)]
  exact congrArg E.eval (funext fun ω ↦ partialR2_eq_angular_ratio z (R ω))

/-- **PL (6.6), the individual report.**  The expected explained fraction of the loss regression
is the trace pairing of `J_H = P_H - P_1` with the angular matrix of the centered squared-loss
vector `z_L = M₁ ℓ`.  One angular loss matrix therefore determines the expected explainabilities
of every fixed loss-regression design containing the intercept, for the same residualization and
cohort design. -/
theorem expected_loss_report_eq_trace (E : ExpFunctional Ω)
    (P1 Ph : Matrix (Fin n) (Fin n) ℝ) (h1 : P1ᵀ = P1) (hh : Phᵀ = Ph) (h1i : P1 * P1 = P1)
    (hc : Ph * P1 = P1) (L : Ω → Fin n → ℝ) :
    E (fun ω ↦ lossExplainedFraction (Ph - P1) (residualMaker P1) (L ω))
      = Matrix.trace ((Ph - P1)
          * angularMatrix E (fun ω ↦ (residualMaker P1).mulVec (L ω))) := by
  rw [← angular_report_identity E (fun ω ↦ (residualMaker P1).mulVec (L ω)) (Ph - P1)]
  exact congrArg E.eval (funext fun ω ↦ lossExplainedFraction_centered P1 Ph h1 hh h1i hc (L ω))

/-! ## PL Proposition 6.4: the exact projective state -/

/-- The projective state fixes its own direction. -/
theorem rankOneProj_mulVec_self (y : Fin d → ℝ) (hy : y ≠ 0) :
    (rankOneProj y).mulVec y = y := by
  rw [rankOneProj_mulVec, inv_mul_cancel₀ (dot_self_ne_zero hy), one_smul]

/-- Rescaling an outer product. -/
theorem vecMulVec_smul (c : ℝ) (y : Fin d → ℝ) :
    Matrix.vecMulVec (c • y) (c • y) = (c ^ 2) • Matrix.vecMulVec y y := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The projective state is scale invariant.**  This is what makes `P(y)` a state of the
projective line through `y` rather than of `y` itself. -/
theorem rankOneProj_smul (c : ℝ) (hc : c ≠ 0) (y : Fin d → ℝ) :
    rankOneProj (c • y) = rankOneProj y := by
  have hdot : dot (c • y) (c • y) = c ^ 2 * dot y y := by
    rw [dot_smul_left, dot_smul_right]
    ring
  rw [rankOneProj, rankOneProj, hdot, vecMulVec_smul, smul_smul]
  congr 1
  rcases eq_or_ne (dot y y) 0 with h | h
  · simp [h]
  · field_simp

/-- **PL Proposition 6.4, the identification step.**  Two nonzero vectors have the same
projective state exactly when they differ by a nonzero scalar.  The manuscript argues through
the one-dimensional range; the direct computation is that `P(y)` fixes `y`.  Only the second
vector needs to be assumed nonzero: if the first were zero its projective state would be the
zero matrix, which cannot fix the nonzero second vector. -/
theorem rankOneProj_eq_iff (y₁ y₂ : Fin d → ℝ) (h₂ : y₂ ≠ 0) :
    rankOneProj y₁ = rankOneProj y₂ ↔ ∃ c : ℝ, c ≠ 0 ∧ y₂ = c • y₁ := by
  constructor
  · intro h
    refine ⟨(dot y₁ y₁)⁻¹ * dot y₁ y₂, ?_, ?_⟩
    · intro hzero
      apply h₂
      have hfix : (rankOneProj y₂).mulVec y₂ = y₂ := rankOneProj_mulVec_self y₂ h₂
      rw [← h, rankOneProj_mulVec, hzero, zero_smul] at hfix
      exact hfix.symm
    · have hfix : (rankOneProj y₂).mulVec y₂ = y₂ := rankOneProj_mulVec_self y₂ h₂
      rw [← h, rankOneProj_mulVec] at hfix
      exact hfix.symm
  · rintro ⟨c, hc, rfl⟩
    exact (rankOneProj_smul c hc y₁).symm

/-- **PL Proposition 6.4, the factorization.**  Every report invariant under nonzero rescaling
of its argument factors through the projective state.  The selection uses classical choice,
which is the measurable-representative step of the manuscript's proof. -/
theorem scale_invariant_report_factors (F : (Fin d → ℝ) → ℝ)
    (hF : ∀ c : ℝ, c ≠ 0 → ∀ y : Fin d → ℝ, F (c • y) = F y) :
    ∃ G : Matrix (Fin d) (Fin d) ℝ → ℝ, ∀ y : Fin d → ℝ, y ≠ 0 → F y = G (rankOneProj y) := by
  classical
  refine ⟨fun M ↦ F (Classical.epsilon fun z : Fin d → ℝ ↦ z ≠ 0 ∧ rankOneProj z = M), ?_⟩
  intro y hy
  have hex : ∃ z : Fin d → ℝ, z ≠ 0 ∧ rankOneProj z = rankOneProj y := ⟨y, hy, rfl⟩
  obtain ⟨_, hzeq⟩ := Classical.epsilon_spec hex
  obtain ⟨c, hc, hyc⟩ := (rankOneProj_eq_iff _ _ hy).mp hzeq
  show F y = F (Classical.epsilon fun z : Fin d → ℝ ↦ z ≠ 0 ∧ rankOneProj z = rankOneProj y)
  rw [← hF c hc (Classical.epsilon fun z : Fin d → ℝ ↦ z ≠ 0 ∧ rankOneProj z = rankOneProj y),
    ← hyc]

/-- **PL Proposition 6.4, sufficiency of the projective law.**  Two laws agree on every bounded
scale-invariant report exactly when they agree on every function of the projective state.  The
hypotheses are the manuscript's domain condition: neither law puts mass on the zero vector. -/
theorem invariant_reports_eq_iff_projective_eq {Ω₁ Ω₂ : Type*} (E₁ : ExpFunctional Ω₁)
    (E₂ : ExpFunctional Ω₂) (V₁ : Ω₁ → Fin d → ℝ) (V₂ : Ω₂ → Fin d → ℝ)
    (h₁ : ∀ ω, V₁ ω ≠ 0) (h₂ : ∀ ω, V₂ ω ≠ 0) :
    (∀ F : (Fin d → ℝ) → ℝ, (∀ c : ℝ, c ≠ 0 → ∀ y : Fin d → ℝ, F (c • y) = F y) →
        E₁ (fun ω ↦ F (V₁ ω)) = E₂ (fun ω ↦ F (V₂ ω)))
      ↔ (∀ G : Matrix (Fin d) (Fin d) ℝ → ℝ,
          E₁ (fun ω ↦ G (rankOneProj (V₁ ω))) = E₂ (fun ω ↦ G (rankOneProj (V₂ ω)))) := by
  constructor
  · intro h G
    refine h (fun y ↦ G (rankOneProj y)) fun c hc y ↦ ?_
    show G (rankOneProj (c • y)) = G (rankOneProj y)
    rw [rankOneProj_smul c hc y]
  · intro h F hF
    obtain ⟨G, hG⟩ := scale_invariant_report_factors F hF
    have e1 : (fun ω ↦ F (V₁ ω)) = fun ω ↦ G (rankOneProj (V₁ ω)) :=
      funext fun ω ↦ hG _ (h₁ ω)
    have e2 : (fun ω ↦ F (V₂ ω)) = fun ω ↦ G (rankOneProj (V₂ ω)) :=
      funext fun ω ↦ hG _ (h₂ ω)
    rw [e1, e2]
    exact h G

/-- **Retaining the radius recovers every homogeneous quadratic error.**  The manuscript's
remark that `y yᵀ = ‖y‖² P(y)`, so that a raw mean squared error computed from a homogeneous
fitted residual is recovered from the projective state together with the squared length. -/
theorem outer_eq_radius_smul_projState (y : Fin d → ℝ) (hy : y ≠ 0) :
    Matrix.vecMulVec y y = (dot y y) • rankOneProj y := by
  rw [rankOneProj, smul_smul, mul_inv_cancel₀ (dot_self_ne_zero hy), one_smul]

/-- **The fixed-prediction loss is not covered by the homogeneous representation.**  The
manuscript states this without a witness; here is one.  With a single coordinate, outcome `1`
and prediction `1`, the loss is `0`, while doubling the outcome makes it `1`.  So `‖y - s‖²` is
not invariant under nonzero rescaling of `y` and must retain its own report input. -/
theorem fixed_prediction_loss_not_scale_invariant :
    ∃ y s : Fin 1 → ℝ, y ≠ 0 ∧
      dot (y - s) (y - s) ≠ dot ((2 : ℝ) • y - s) ((2 : ℝ) • y - s) := by
  refine ⟨fun _ ↦ 1, fun _ ↦ 1, ?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    norm_num at h0
  · simp only [dot, Descent.Core.innerSum, Fin.sum_univ_one, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    norm_num

end

end Descent.Portability.AngularReportClosure
