/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EvolutionaryForecastMinimax
import Descent.Portability.DiscountedObservability
import Mathlib.Analysis.InnerProductSpace.l2Space

assert_below Descent.Decision Descent.Program

/-!
The infinite discounted forecast is an actual square-summable Hilbert trajectory.
Its bounded linear operator and Gramian are derived from finite Markov evolution,
so the spectral measurement theorem applies to the complete infinite horizon.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Matrix ENNReal

namespace Descent.Portability.DiscountedForecastMinimax

open EvolutionaryObservability DiscountedObservability EvolutionaryForecastMinimax
open AdaptiveLinearMeasurements SpectralMeasurementMinimax

variable {S I R : Type*} [Fintype S] [DecidableEq S]
  [Fintype I] [Fintype R] [DecidableEq R]

abbrev Trajectory (I : Type*) [Fintype I] := lp (fun _ : ℕ ↦ EuclideanSpace ℝ I) 2

noncomputable def sequence (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (discount : ℝ) (direction : S → ℝ) (time : ℕ) : EuclideanSpace ℝ I :=
  Real.sqrt (discount ^ time) •
    WithLp.toLp 2 ((evolvedReports kernel reports time).transpose *ᵥ direction)

theorem sequence_norm (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (discount : ℝ) (hnonneg : 0 ≤ discount) (direction : S → ℝ) (time : ℕ) :
    ‖sequence kernel reports discount direction time‖ ^ 2 =
      discount ^ time * ∑ report,
        ((evolvedReports kernel reports time).transpose *ᵥ direction) report ^ 2 := by
  rw [sequence, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (pow_nonneg hnonneg time), EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  rfl

theorem sequence_mem (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1) (direction : S → ℝ) :
    Memℓp (sequence kernel reports discount direction) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  simp_rw [sequence_norm kernel reports discount hnonneg direction]
  exact discounted_loss_summable kernel reports discount hnonneg hlt direction

noncomputable def trajectory (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1)
    (direction : S → ℝ) : Trajectory I :=
  ⟨sequence kernel reports discount direction,
    sequence_mem kernel reports discount hnonneg hlt direction⟩

theorem trajectory_norm (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1) (direction : S → ℝ) :
    ‖trajectory kernel reports discount hnonneg hlt direction‖ ^ 2 =
      direction ⬝ᵥ discountedGramian kernel reports discount *ᵥ direction := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
    (trajectory kernel reports discount hnonneg hlt direction)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [h]
  change (∑' time, ‖sequence kernel reports discount direction time‖ ^ 2) = _
  simp_rw [sequence_norm kernel reports discount hnonneg direction]
  exact discounted_loss_eq_quadratic kernel reports discount hnonneg hlt direction

noncomputable def forecastLinear (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1) (residual : Matrix S R ℝ) :
    EuclideanSpace ℝ R →ₗ[ℝ] Trajectory I where
  toFun vector := trajectory kernel reports discount hnonneg hlt
    (residual *ᵥ WithLp.ofLp vector)
  map_add' first second := by
    ext time report
    simp [trajectory, sequence, Matrix.mulVec_add]
    ring
  map_smul' scalar vector := by
    ext time report
    simp [trajectory, sequence, Matrix.mulVec_smul]
    ring

noncomputable def forecastOperator (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1) (residual : Matrix S R ℝ) :
    EuclideanSpace ℝ R →L[ℝ] Trajectory I :=
  (forecastLinear kernel reports discount hnonneg hlt residual).toContinuousLinearMap

omit [DecidableEq R] in
/-- The infinite trajectory's norm is exactly the residual discounted Gramian form. -/
theorem forecastOperator_norm (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1) (residual : Matrix S R ℝ)
    (vector : EuclideanSpace ℝ R) :
    ‖forecastOperator kernel reports discount hnonneg hlt residual vector‖ ^ 2 =
      WithLp.ofLp vector ⬝ᵥ
        (residual.transpose * discountedGramian kernel reports discount * residual) *ᵥ
          WithLp.ofLp vector := by
  change ‖trajectory kernel reports discount hnonneg hlt
    (residual *ᵥ WithLp.ofLp vector)‖ ^ 2 = _
  rw [trajectory_norm]
  simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem discountedGramian_symmetric (kernel : S → FiniteReportLaw S)
    (reports : Matrix S I ℝ) (discount : ℝ) :
    (discountedGramian kernel reports discount).transpose =
      discountedGramian kernel reports discount := by
  unfold discountedGramian discountedSum
  rw [Matrix.transpose_tsum]
  apply tsum_congr
  intro time
  rw [discountedTerm, Matrix.transpose_smul, transported_report_gramian]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]

private theorem symmetric_eq_of_quadratic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (first second : E →L[ℝ] E) (hfirst : star first = first) (hsecond : star second = second)
    (hquadratic : ∀ vector, inner ℝ vector (first vector) = inner ℝ vector (second vector)) :
    first = second := by
  have hcross (operator : E →L[ℝ] E) (hself : star operator = operator) (x y : E) :
      inner ℝ x (operator y) = inner ℝ y (operator x) := by
    have h := operator.adjoint_inner_right x y
    change inner ℝ x (star operator y) = inner ℝ (operator x) y at h
    rw [hself] at h
    exact h.trans (real_inner_comm _ _)
  ext vector
  apply ext_inner_left ℝ
  intro other
  have h := hquadratic (vector + other)
  simp only [map_add, inner_add_left, inner_add_right] at h
  have hf := hcross first hfirst vector other
  have hs := hcross second hsecond vector other
  linarith [hquadratic vector, hquadratic other]

/-- The discounted trajectory Gram operator equals `Dᵀ G∞ D`, in Euclidean coordinates. -/
theorem forecastOperator_gram (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1) (residual : Matrix S R ℝ) :
    FiniteTargetSpectrum.gram (forecastOperator kernel reports discount hnonneg hlt residual) =
      euclideanOperator (residual.transpose * discountedGramian kernel reports discount *
        residual) := by
  let target := forecastOperator kernel reports discount hnonneg hlt residual
  let matrix := residual.transpose * discountedGramian kernel reports discount * residual
  have hmatrix : matrix.transpose = matrix := by
    simp only [matrix, Matrix.transpose_mul, Matrix.transpose_transpose,
      discountedGramian_symmetric, Matrix.mul_assoc]
  apply symmetric_eq_of_quadratic
  · change star (target.adjoint.comp target) = target.adjoint.comp target
    simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  · change (euclideanOperator matrix).adjoint = euclideanOperator matrix
    rw [euclideanOperator_adjoint, hmatrix]
  · intro vector
    have hnorm := target.apply_norm_sq_eq_inner_adjoint_right vector
    change ‖target vector‖ ^ 2 = inner ℝ vector (FiniteTargetSpectrum.gram target vector) at hnorm
    rw [← hnorm]
    rw [forecastOperator_norm]
    rw [EuclideanSpace.inner_eq_star_dotProduct, euclideanOperator_apply]
    simp only [WithLp.ofLp_toLp, star_trivial, dotProduct_comm]

theorem trajectory_add (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1) (first second : S → ℝ) :
    trajectory kernel reports discount hnonneg hlt (first + second) =
      trajectory kernel reports discount hnonneg hlt first +
        trajectory kernel reports discount hnonneg hlt second := by
  ext time report
  simp [trajectory, sequence, Matrix.mulVec_add]
  ring

noncomputable def lawTrajectory (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1)
    (initial : FiniteReportLaw S) : Trajectory I :=
  trajectory kernel reports discount hnonneg hlt initial.mass

/-- Every Hilbert-trajectory coordinate is the expected report under the actual
propagated probability law, multiplied by its declared discount weight. -/
theorem lawTrajectory_coordinate (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1)
    (initial : FiniteReportLaw S) (time : ℕ) (report : I) :
    lawTrajectory kernel reports discount hnonneg hlt initial time report =
      Real.sqrt (discount ^ time) *
        (initial.bind (powerLaw kernel time)).expectation (fun state ↦ reports state report) := by
  change Real.sqrt (discount ^ time) *
    ((evolvedReports kernel reports time).transpose *ᵥ initial.mass) report = _
  rw [FiniteReportLaw.expectation_bind]
  simp only [FiniteReportLaw.expectation, powerLaw_mass, evolvedReports,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro target _
  ring

omit [DecidableEq R] in
theorem lawTrajectory_affine (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1)
    (center : S → ℝ) (residual : Matrix S R ℝ) (radius : ℝ)
    (hfeasible : FeasibleBall center residual radius) (vector : EuclideanSpace ℝ R)
    (hvector : ‖vector‖ ≤ radius) :
    lawTrajectory kernel reports discount hnonneg hlt
        (initialLaw center residual radius hfeasible vector hvector) =
      trajectory kernel reports discount hnonneg hlt center +
        forecastOperator kernel reports discount hnonneg hlt residual vector := by
  change trajectory kernel reports discount hnonneg hlt
    (center + residual *ᵥ WithLp.ofLp vector) = _
  rw [trajectory_add]
  rfl

/-- The exact spectral minimax law for the complete discounted trajectory. All
initial laws in the residual ball must be feasible; arbitrary adaptive prediction
procedures are allowed, and the residual Gramian is identified explicitly. -/
theorem adaptive_discounted_minimax (kernel : S → FiniteReportLaw S) (reports : Matrix S I ℝ)
    (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1)
    (center : S → ℝ) (residual : Matrix S R ℝ) (radius : ℝ) (hradius : 0 ≤ radius)
    (hfeasible : FeasibleBall center residual radius) (queries : ℕ) :
    let target := forecastOperator kernel reports discount hnonneg hlt residual
    IsLeast {risk : ℝ | ∃ procedure : Procedure (EuclideanSpace ℝ R) (Trajectory I) queries,
      ∀ vector : EuclideanSpace ℝ R, ∀ hvector : ‖vector‖ ≤ radius,
        ‖lawTrajectory kernel reports discount hnonneg hlt
            (initialLaw center residual radius hfeasible vector hvector) -
          procedure.run vector‖ ^ 2 ≤ risk}
      (radius ^ 2 * residualEigenvalue target queries) ∧
    FiniteTargetSpectrum.gram target =
      euclideanOperator (residual.transpose * discountedGramian kernel reports discount *
        residual) := by
  dsimp only
  let target := forecastOperator kernel reports discount hnonneg hlt residual
  let base := trajectory kernel reports discount hnonneg hlt center
  have hspectral := adaptive_minimax_all_budgets target queries radius hradius
  refine ⟨?_, forecastOperator_gram _ _ _ _ _ residual⟩
  constructor
  · obtain ⟨procedure, hprocedure⟩ := hspectral.1
    refine ⟨translatePrediction base procedure, ?_⟩
    intro vector hvector
    rw [lawTrajectory_affine, translatePrediction_run]
    change ‖base + target vector - (base + procedure.run vector)‖ ^ 2 ≤ _
    simpa only [add_sub_add_left_eq_sub] using hprocedure vector hvector
  · rintro risk ⟨procedure, hprocedure⟩
    apply hspectral.2
    refine ⟨translatePrediction (-base) procedure, ?_⟩
    intro vector hvector
    have h := hprocedure vector hvector
    rw [lawTrajectory_affine] at h
    rw [translatePrediction_run]
    change ‖target vector - (-base + procedure.run vector)‖ ^ 2 ≤ _
    convert h using 1
    congr 2
    dsimp only [target, base]
    abel

end Descent.Portability.DiscountedForecastMinimax
