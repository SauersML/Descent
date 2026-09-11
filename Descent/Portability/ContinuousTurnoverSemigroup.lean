/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BanachEulerExponential
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension

assert_below Descent.Decision Descent.Program

/-!
# Passing a finite-state comparison to the continuous-time semigroup

Infrastructure for the continuous-time form of DC Theorem 3.1 / PL Theorem 5.3: a pointwise
inequality between Euler approximants of two finite-state generators passes to the
semigroups they generate, using the Euler limit of
`Descent.Portability.BanachEulerExponential`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ContinuousTurnoverSemigroup

open scoped Matrix.Norms.Operator

noncomputable section

/-- Evaluating a matrix against a fixed vector at a fixed coordinate is linear. -/
def mulVecEntry (N : ℕ) (v : Fin N → ℝ) (j : Fin N) :
    Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ where
  toFun M := M.mulVec v j
  map_add' M M' := by simp [Matrix.add_mulVec]
  map_smul' c M := by simp [Matrix.smul_mulVec_assoc]

/-- **Euler limits transfer a pointwise inequality to the generated semigroups.** -/
theorem exp_mulVec_le_of_euler {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ)
    (j : Fin N)
    (h : ∀ m : ℕ, ((1 + (m : ℝ)⁻¹ • A) ^ m).mulVec v j
      ≤ ((1 + (m : ℝ)⁻¹ • B) ^ m).mulVec v j) :
    (NormedSpace.exp ℝ A).mulVec v j ≤ (NormedSpace.exp ℝ B).mulVec v j := by
  have hcont : Continuous (mulVecEntry N v j) :=
    (mulVecEntry N v j).continuous_of_finiteDimensional
  have hA := (hcont.tendsto (NormedSpace.exp ℝ A)).comp
    (BanachEulerExponential.euler_tends_exp A)
  have hB := (hcont.tendsto (NormedSpace.exp ℝ B)).comp
    (BanachEulerExponential.euler_tends_exp B)
  exact le_of_tendsto_of_tendsto hA hB (Filter.Eventually.of_forall h)

end

end Descent.Portability.ContinuousTurnoverSemigroup
