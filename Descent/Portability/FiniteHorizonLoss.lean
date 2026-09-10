/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MarkovCoarseGraining

assert_below Descent.Decision Descent.Program

/-!
Exact stationary finite-horizon prediction experiments. The frozen predictor and
optimal transported predictor have different losses. These identities apply to
any finite stationary transition kernel, including a finite CTMC semigroup.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Matrix

namespace Descent.Portability.FiniteHorizonLoss

variable {S : Type*} [Fintype S] [DecidableEq S]

noncomputable def inner (law : FiniteReportLaw S) (first second : S → ℝ) : ℝ :=
  ∑ state, law.mass state * first state * second state

noncomputable def energy (law : FiniteReportLaw S) (report : S → ℝ) : ℝ :=
  inner law report report

noncomputable def predict (kernel : S → FiniteReportLaw S) (report : S → ℝ) : S → ℝ :=
  fun source ↦ (kernel source).expectation report

noncomputable def risk (law : FiniteReportLaw S) (kernel : S → FiniteReportLaw S)
    (report predictor : S → ℝ) : ℝ :=
  ∑ source, law.mass source *
    ∑ target, (kernel source).mass target * (report target - predictor source) ^ 2

def Stationary (law : FiniteReportLaw S) (kernel : S → FiniteReportLaw S) : Prop :=
  ∀ target, ∑ source, law.mass source * (kernel source).mass target = law.mass target

omit [DecidableEq S] in
theorem risk_nonneg (law : FiniteReportLaw S) (kernel : S → FiniteReportLaw S)
    (report predictor : S → ℝ) : 0 ≤ risk law kernel report predictor := by
  apply Finset.sum_nonneg
  intro source _
  apply mul_nonneg (law.mass_nonneg source)
  apply Finset.sum_nonneg
  intro target _
  exact mul_nonneg ((kernel source).mass_nonneg target) (sq_nonneg _)

omit [DecidableEq S] in
theorem energy_nonneg (law : FiniteReportLaw S) (report : S → ℝ) :
    0 ≤ energy law report := by
  unfold energy inner
  apply Finset.sum_nonneg
  intro state _
  nlinarith [law.mass_nonneg state, sq_nonneg (report state)]

omit [DecidableEq S] in
/-- Expanding the actual joint-law squared loss uses stationarity only for the
future report's second moment. -/
theorem risk_expansion (law : FiniteReportLaw S) (kernel : S → FiniteReportLaw S)
    (hstationary : Stationary law kernel) (report predictor : S → ℝ) :
    risk law kernel report predictor = energy law report + energy law predictor -
      2 * inner law predictor (predict kernel report) := by
  have hrow (source : S) :
      (∑ target, (kernel source).mass target * (report target - predictor source) ^ 2) =
      (∑ target, (kernel source).mass target * report target ^ 2) + predictor source ^ 2 -
        2 * predictor source * predict kernel report source := by
    simp only [predict, FiniteReportLaw.expectation]
    calc
      _ = ∑ target, ((kernel source).mass target * report target ^ 2 +
          (kernel source).mass target * predictor source ^ 2 -
          2 * predictor source * ((kernel source).mass target * report target)) := by
        apply Finset.sum_congr rfl
        intro target _
        ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
          ← Finset.mul_sum, (kernel source).mass_sum, one_mul]
  have hsecond : (∑ source, law.mass source *
      ∑ target, (kernel source).mass target * report target ^ 2) = energy law report := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    unfold energy inner
    apply Finset.sum_congr rfl
    intro target _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hstationary target]
    ring
  unfold risk
  simp_rw [hrow, mul_sub, mul_add]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hsecond]
  unfold energy inner
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro state _
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro state _
    ring

omit [DecidableEq S] in
/-- The stale observable has loss twice its stationary energy minus twice its
lagged correlation. No reversibility is assumed. -/
theorem stale_loss (law : FiniteReportLaw S) (kernel : S → FiniteReportLaw S)
    (hstationary : Stationary law kernel) (report : S → ℝ) :
    risk law kernel report report =
      2 * energy law report - 2 * inner law report (predict kernel report) := by
  rw [risk_expansion law kernel hstationary]
  ring

omit [DecidableEq S] in
theorem energy_difference (law : FiniteReportLaw S) (first second : S → ℝ) :
    energy law (first - second) =
      energy law first + energy law second - 2 * inner law first second := by
  unfold energy inner
  simp only [Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro state _
  ring

omit [DecidableEq S] in
/-- The exact excess risk is the squared distance from the transported predictor. -/
theorem optimal_prediction_decomposition (law : FiniteReportLaw S)
    (kernel : S → FiniteReportLaw S) (hstationary : Stationary law kernel)
    (report predictor : S → ℝ) :
    risk law kernel report predictor =
      energy law report - energy law (predict kernel report) +
        energy law (predictor - predict kernel report) := by
  rw [risk_expansion law kernel hstationary, energy_difference]
  ring

omit [DecidableEq S] in
theorem optimal_prediction_risk (law : FiniteReportLaw S)
    (kernel : S → FiniteReportLaw S) (hstationary : Stationary law kernel)
    (report : S → ℝ) :
    risk law kernel report (predict kernel report) =
      energy law report - energy law (predict kernel report) := by
  rw [risk_expansion law kernel hstationary]
  unfold energy
  ring

omit [DecidableEq S] in
theorem optimal_prediction_minimizes (law : FiniteReportLaw S)
    (kernel : S → FiniteReportLaw S) (hstationary : Stationary law kernel)
    (report predictor : S → ℝ) :
    risk law kernel report (predict kernel report) ≤ risk law kernel report predictor := by
  rw [optimal_prediction_risk law kernel hstationary,
    optimal_prediction_decomposition law kernel hstationary]
  exact le_add_of_nonneg_right (energy_nonneg _ _)

/-- The backward transition kernel is the adjoint in the stationary weighted
inner product. Strictly positive stationary masses avoid quotienting null states. -/
noncomputable def reverseKernel (law : FiniteReportLaw S)
    (kernel : S → FiniteReportLaw S) (hstationary : Stationary law kernel)
    (hpositive : ∀ state, 0 < law.mass state) (target : S) : FiniteReportLaw S where
  mass source := law.mass source * (kernel source).mass target / law.mass target
  mass_nonneg source := div_nonneg
    (mul_nonneg (law.mass_nonneg source) ((kernel source).mass_nonneg target))
    (law.mass_nonneg target)
  mass_sum := by
    rw [← Finset.sum_div, hstationary target]
    exact div_self (ne_of_gt (hpositive target))

omit [DecidableEq S] in
/-- The adjoint identity follows from the actual reversed joint law. -/
theorem reverse_adjoint (law : FiniteReportLaw S) (kernel : S → FiniteReportLaw S)
    (hstationary : Stationary law kernel) (hpositive : ∀ state, 0 < law.mass state)
    (first second : S → ℝ) :
    inner law first (predict (reverseKernel law kernel hstationary hpositive) second) =
      inner law (predict kernel first) second := by
  unfold inner predict FiniteReportLaw.expectation
  simp only [reverseKernel, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro target _
  field_simp [ne_of_gt (hpositive target)]

noncomputable def lossMatrix (law : FiniteReportLaw S)
    (kernel : S → FiniteReportLaw S) (hstationary : Stationary law kernel)
    (hpositive : ∀ state, 0 < law.mass state) : Matrix S S ℝ :=
  (2 : ℝ) • 1 - InterleavedMutationExponential.kernelMatrix kernel -
    InterleavedMutationExponential.kernelMatrix
      (reverseKernel law kernel hstationary hpositive)

/-- The exact finite-horizon stale-loss operator is `2I - P - P*`, where the
adjoint is with respect to the stationary law, not an unweighted transpose. -/
theorem stale_loss_operator (law : FiniteReportLaw S)
    (kernel : S → FiniteReportLaw S) (hstationary : Stationary law kernel)
    (hpositive : ∀ state, 0 < law.mass state) (report : S → ℝ) :
    risk law kernel report report =
      inner law report (lossMatrix law kernel hstationary hpositive *ᵥ report) := by
  have hmul (transition : S → FiniteReportLaw S) :
      InterleavedMutationExponential.kernelMatrix transition *ᵥ report =
        predict transition report := by
    ext state
    rfl
  have hsymm : inner law (predict kernel report) report =
      inner law report (predict kernel report) := by
    unfold inner
    apply Finset.sum_congr rfl
    intro state _
    ring
  rw [stale_loss law kernel hstationary]
  unfold lossMatrix
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    hmul, hmul]
  have hexpand : inner law report
      ((2 : ℝ) • report - predict kernel report -
        predict (reverseKernel law kernel hstationary hpositive) report) =
      2 * energy law report - inner law report (predict kernel report) -
        inner law report
          (predict (reverseKernel law kernel hstationary hpositive) report) := by
    unfold energy inner
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib, Finset.mul_sum]
    congr 2
    apply Finset.sum_congr rfl
    intro state _
    ring
  rw [hexpand, reverse_adjoint, hsymm]
  ring

/-- Positivity is derived from the squared-loss experiment. -/
theorem lossMatrix_positive (law : FiniteReportLaw S)
    (kernel : S → FiniteReportLaw S) (hstationary : Stationary law kernel)
    (hpositive : ∀ state, 0 < law.mass state) (report : S → ℝ) :
    0 ≤ inner law report (lossMatrix law kernel hstationary hpositive *ᵥ report) := by
  rw [← stale_loss_operator]
  exact risk_nonneg _ _ _ _

end Descent.Portability.FiniteHorizonLoss
