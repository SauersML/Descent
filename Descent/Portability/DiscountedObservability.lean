/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EvolutionaryObservability

assert_below Descent.Decision Descent.Program

/-!
The infinite discounted observability Gramian of a finite evolutionary kernel.
Absolute convergence and uniqueness follow from probability-row contraction,
without reversibility, irreducibility, or a spectral-gap assumption.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Matrix

namespace Descent.Portability.DiscountedObservability

open EvolutionaryObservability InterleavedMutationExponential
variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]

noncomputable def transported (kernel : S → FiniteReportLaw S) (matrix : Matrix S S ℝ)
    (time : ℕ) : Matrix S S ℝ :=
  kernelMatrix kernel ^ time * matrix * (kernelMatrix kernel ^ time).transpose

/-- Each transported coordinate is a convex combination of original coordinates. -/
theorem transported_expectation (kernel : S → FiniteReportLaw S) (matrix : Matrix S S ℝ)
    (time : ℕ) (first second : S) :
    transported kernel matrix time first second =
      (powerLaw kernel time first).expectation (fun left ↦
        (powerLaw kernel time second).expectation (fun right ↦ matrix left right)) := by
  simp only [transported, Matrix.mul_apply, Matrix.transpose_apply,
    FiniteReportLaw.expectation, powerLaw_mass, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  ring

theorem transported_abs_le (kernel : S → FiniteReportLaw S) (matrix : Matrix S S ℝ)
    (bound : ℝ) (hbound : ∀ first second, |matrix first second| ≤ bound)
    (time : ℕ) (first second : S) :
    |transported kernel matrix time first second| ≤ bound := by
  rw [transported_expectation]
  apply expectation_abs_le
  intro left
  exact expectation_abs_le _ _ _ (hbound left)

noncomputable def entryBound (matrix : Matrix S S ℝ) : ℝ :=
  ∑ first, ∑ second, |matrix first second|

omit [DecidableEq S] in
theorem entryBound_nonneg (matrix : Matrix S S ℝ) : 0 ≤ entryBound matrix :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

omit [DecidableEq S] in
theorem abs_le_entryBound (matrix : Matrix S S ℝ) (first second : S) :
    |matrix first second| ≤ entryBound matrix := by
  apply le_trans (Finset.single_le_sum (fun index _ ↦ abs_nonneg (matrix first index))
    (Finset.mem_univ second))
  exact Finset.single_le_sum
    (fun index _ ↦ Finset.sum_nonneg fun target _ ↦ abs_nonneg (matrix index target))
    (Finset.mem_univ first)

noncomputable def discountedTerm (kernel : S → FiniteReportLaw S)
    (matrix : Matrix S S ℝ) (discount : ℝ) (time : ℕ) : Matrix S S ℝ :=
  discount ^ time • transported kernel matrix time

theorem discountedTerm_summable (kernel : S → FiniteReportLaw S)
    (matrix : Matrix S S ℝ) (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1) :
    Summable (discountedTerm kernel matrix discount) := by
  apply Pi.summable.mpr
  intro first
  apply Pi.summable.mpr
  intro second
  apply ((summable_geometric_of_lt_one hnonneg hlt).mul_right (entryBound matrix)).of_norm_bounded
  intro time
  change |discount ^ time * transported kernel matrix time first second| ≤
    discount ^ time * entryBound matrix
  rw [abs_mul, abs_of_nonneg (pow_nonneg hnonneg time)]
  exact mul_le_mul_of_nonneg_left
    (transported_abs_le kernel matrix _ (abs_le_entryBound matrix) time first second)
    (pow_nonneg hnonneg time)

noncomputable def discountedSum (kernel : S → FiniteReportLaw S)
    (matrix : Matrix S S ℝ) (discount : ℝ) : Matrix S S ℝ :=
  ∑' time, discountedTerm kernel matrix discount time

theorem transported_succ (kernel : S → FiniteReportLaw S) (matrix : Matrix S S ℝ)
    (time : ℕ) :
    transported kernel matrix (time + 1) =
      kernelMatrix kernel * transported kernel matrix time * (kernelMatrix kernel).transpose := by
  simp only [transported, pow_succ', Matrix.transpose_mul, Matrix.mul_assoc]

theorem discountedTerm_succ (kernel : S → FiniteReportLaw S)
    (matrix : Matrix S S ℝ) (discount : ℝ) (time : ℕ) :
    discountedTerm kernel matrix discount (time + 1) =
      discount • (kernelMatrix kernel * discountedTerm kernel matrix discount time *
        (kernelMatrix kernel).transpose) := by
  simp only [discountedTerm, transported_succ, pow_succ', Matrix.mul_smul,
    Matrix.smul_mul, smul_smul]

/-- The convergent discounted series solves the discrete Lyapunov equation. -/
theorem discountedSum_equation (kernel : S → FiniteReportLaw S)
    (matrix : Matrix S S ℝ) (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1) :
    discountedSum kernel matrix discount = matrix + discount •
      (kernelMatrix kernel * discountedSum kernel matrix discount *
        (kernelMatrix kernel).transpose) := by
  have hs := discountedTerm_summable kernel matrix discount hnonneg hlt
  have hzero : discountedTerm kernel matrix discount 0 = matrix := by
    simp [discountedTerm, transported]
  calc
    discountedSum kernel matrix discount = discountedTerm kernel matrix discount 0 +
        ∑' time, discountedTerm kernel matrix discount (time + 1) := hs.tsum_eq_zero_add
    _ = matrix + discount • (kernelMatrix kernel * discountedSum kernel matrix discount *
        (kernelMatrix kernel).transpose) := by
      rw [hzero]
      congr 1
      calc
          (∑' time, discountedTerm kernel matrix discount (time + 1)) =
              ∑' time, discount • (kernelMatrix kernel *
                discountedTerm kernel matrix discount time *
                (kernelMatrix kernel).transpose) := tsum_congr (discountedTerm_succ _ _ _)
          _ = discount • (kernelMatrix kernel * discountedSum kernel matrix discount *
              (kernelMatrix kernel).transpose) := by
            rw [tsum_const_smul'', (hs.mul_left (kernelMatrix kernel)).tsum_mul_right,
              hs.tsum_mul_left]
            rfl

/-- A homogeneous fixed point must shrink by every discount power. -/
theorem fixed_point_iteration (kernel : S → FiniteReportLaw S)
    (matrix : Matrix S S ℝ) (discount : ℝ)
    (hfixed : matrix = discount • (kernelMatrix kernel * matrix * (kernelMatrix kernel).transpose))
    (time : ℕ) : matrix = discountedTerm kernel matrix discount time := by
  induction time with
  | zero => simp [discountedTerm, transported]
  | succ time ih =>
      rw [discountedTerm_succ, ← ih]
      exact hfixed

theorem homogeneous_fixed_point_zero (kernel : S → FiniteReportLaw S)
    (matrix : Matrix S S ℝ) (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1)
    (hfixed : matrix = discount •
      (kernelMatrix kernel * matrix * (kernelMatrix kernel).transpose)) :
    matrix = 0 := by
  ext first second
  have hbound (time : ℕ) : |matrix first second| ≤ discount ^ time * entryBound matrix := by
    have heq := congrArg (fun value : Matrix S S ℝ ↦ value first second)
      (fixed_point_iteration kernel matrix discount hfixed time)
    dsimp only at heq
    rw [heq]
    change |discount ^ time * transported kernel matrix time first second| ≤ _
    rw [abs_mul, abs_of_nonneg (pow_nonneg hnonneg time)]
    exact mul_le_mul_of_nonneg_left
      (transported_abs_le kernel matrix _ (abs_le_entryBound matrix) time first second)
      (pow_nonneg hnonneg time)
  have hlimit : Filter.Tendsto (fun time : ℕ ↦ discount ^ time * entryBound matrix)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hnonneg hlt).mul_const (entryBound matrix)
  have hz : |matrix first second| ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlimit (Filter.Eventually.of_forall hbound)
  exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))

/-- No ergodicity assumption is needed for uniqueness when the discount is below one. -/
theorem discountedSum_unique (kernel : S → FiniteReportLaw S)
    (matrix : Matrix S S ℝ) (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1)
    (candidate : Matrix S S ℝ)
    (hcandidate : candidate = matrix + discount •
      (kernelMatrix kernel * candidate * (kernelMatrix kernel).transpose)) :
    candidate = discountedSum kernel matrix discount := by
  apply sub_eq_zero.mp
  apply homogeneous_fixed_point_zero kernel _ discount hnonneg hlt
  have hexact := discountedSum_equation kernel matrix discount hnonneg hlt
  calc
    candidate - discountedSum kernel matrix discount =
        (matrix + discount • (kernelMatrix kernel * candidate * (kernelMatrix kernel).transpose)) -
          (matrix + discount • (kernelMatrix kernel * discountedSum kernel matrix discount *
            (kernelMatrix kernel).transpose)) := congrArg₂ (· - ·) hcandidate hexact
    _ = _ := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, smul_sub]
      abel

noncomputable def discountedGramian (kernel : S → FiniteReportLaw S)
    (reports : Matrix S I ℝ) (discount : ℝ) : Matrix S S ℝ :=
  discountedSum kernel (reports * reports.transpose) discount

/-- The report's infinite-horizon Gramian exists and is the unique Lyapunov solution. -/
theorem discountedGramian_exists_unique (kernel : S → FiniteReportLaw S)
    (reports : Matrix S I ℝ) (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1) :
    ∃! gramian : Matrix S S ℝ, gramian = reports * reports.transpose + discount •
      (kernelMatrix kernel * gramian * (kernelMatrix kernel).transpose) := by
  refine ⟨discountedGramian kernel reports discount, ?_, ?_⟩
  · exact discountedSum_equation _ _ _ hnonneg hlt
  · intro candidate hcandidate
    exact discountedSum_unique _ _ _ hnonneg hlt _ hcandidate


/-- The transported base matrix is the outer product of the actual future reports. -/
theorem transported_report_gramian (kernel : S → FiniteReportLaw S)
    (reports : Matrix S I ℝ) (time : ℕ) :
    transported kernel (reports * reports.transpose) time =
      evolvedReports kernel reports time * (evolvedReports kernel reports time).transpose := by
  simp only [transported, evolvedReports, Matrix.transpose_mul, Matrix.mul_assoc]

noncomputable def quadraticLinear (direction : S → ℝ) : Matrix S S ℝ →ₗ[ℝ] ℝ where
  toFun matrix := direction ⬝ᵥ matrix *ᵥ direction
  map_add' first second := by simp [Matrix.add_mulVec, dotProduct_add]
  map_smul' scalar matrix := by simp [Matrix.smul_mulVec, dotProduct_smul]

theorem discountedTerm_quadratic (kernel : S → FiniteReportLaw S)
    (reports : Matrix S I ℝ) (discount : ℝ) (direction : S → ℝ) (time : ℕ) :
    quadraticLinear direction (discountedTerm kernel (reports * reports.transpose) discount time) =
      discount ^ time * ∑ report,
        ((evolvedReports kernel reports time).transpose *ᵥ direction) report ^ 2 := by
  have heq := forecastLoss_eq_quadratic
    (fun _ : Unit ↦ evolvedReports kernel reports time) (fun _ ↦ discount ^ time) direction
  simpa only [forecastLoss, gramian, Finset.univ_unique, Finset.sum_singleton,
    discountedTerm, quadraticLinear, LinearMap.coe_mk, AddHom.coe_mk,
    transported_report_gramian] using heq.symm

/-- The infinite discounted forecast loss is summable for every initial direction. -/
theorem discounted_loss_summable (kernel : S → FiniteReportLaw S)
    (reports : Matrix S I ℝ) (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1)
    (direction : S → ℝ) :
    Summable (fun time : ℕ ↦ discount ^ time * ∑ report,
      ((evolvedReports kernel reports time).transpose *ᵥ direction) report ^ 2) := by
  let linear : Matrix S S ℝ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (quadraticLinear direction)
  have hs := linear.summable
    (discountedTerm_summable kernel (reports * reports.transpose) discount hnonneg hlt)
  simpa only [linear, LinearMap.coe_toContinuousLinearMap', discountedTerm_quadratic] using hs

/-- The limiting Gramian evaluates the complete infinite discounted trajectory loss. -/
theorem discounted_loss_eq_quadratic (kernel : S → FiniteReportLaw S)
    (reports : Matrix S I ℝ) (discount : ℝ) (hnonneg : 0 ≤ discount) (hlt : discount < 1)
    (direction : S → ℝ) :
    (∑' time : ℕ, discount ^ time * ∑ report,
      ((evolvedReports kernel reports time).transpose *ᵥ direction) report ^ 2) =
        direction ⬝ᵥ discountedGramian kernel reports discount *ᵥ direction := by
  let linear : Matrix S S ℝ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (quadraticLinear direction)
  have hs := discountedTerm_summable kernel (reports * reports.transpose) discount hnonneg hlt
  have heq := linear.map_tsum hs
  simpa only [linear, LinearMap.coe_toContinuousLinearMap', discountedTerm_quadratic,
    discountedGramian, discountedSum] using heq.symm

end Descent.Portability.DiscountedObservability
