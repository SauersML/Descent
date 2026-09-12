/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IntegrableRateRealization
import Descent.Portability.IntegrableGeneratorPropagator
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Data.Matrix.Block
import Mathlib.Topology.Instances.Matrix

assert_below Descent.Decision Descent.Program

/-!
# The derivative of a fundamental matrix along an affine family of generator paths

`LinearFundamentalMatrix` constructs the fundamental matrix `U` of `U' = A(t) U`, `U(0) = 1`, for a
continuous generator path, and `IntegrableGeneratorPropagator` bounds how far it moves when the
path moves.  This module differentiates it in a parameter that enters the path affinely,
`A_θ(s) = A(s) + θ B(s)`.

The block system.  For continuous blocks `P`, `C`, `D`, the lower-triangular path `[[P, 0], [C, D]]`
over `ι ⊕ ι` (`blockPath`) has a fundamental matrix whose upper-left block is the fundamental matrix
of `P` (`toBlocks₁₁_fundamentalMatrix_blockPath`) and whose lower-left block `X` solves the forced
equation `X(t) = ∫₀ᵗ (C U_P + D X)` (`toBlocks₂₁_fundamentalMatrix_blockPath_eq_integral`).  Both
come from the integral equation of the block path and the uniqueness of continuous solutions,
`IntegrableRateRealization.eq_of_integral_eq`.

The exact difference.  With `P = A + εB`, `C = B` and `D = A`, the difference `U_{A+εB} - U_A` is
`ε X_ε` on the horizon (`fundamentalMatrix_line_sub`): `U_{A+εB} - ε X_ε` solves the equation of
`A`, so it is `U_A`.

The limit.  The block paths at `ε` and at `0` differ by `ε [[B, 0], [0, 0]]`, so the variation of
constants bound `IntegrableGeneratorPropagator.norm_fundamentalMatrix_sub_le_exp_integral` keeps
their fundamental matrices at the horizon within `|ε| K` for `|ε| ≤ 1`
(`norm_fundamentalMatrix_blockLine_sub_le`).  So every entry of `ε ↦ U_{A+εB}(T)` has as derivative
at `0` the corresponding entry of the lower-left block of the fundamental matrix of
`[[A, 0], [B, A]]` (`hasDerivAt_fundamentalMatrix_line`), and at any `θ₀` the same with `A + θ₀ B`
in place of `A` (`hasDerivAt_fundamentalMatrix_affinePath`).  Paired with vectors, `c · U v` has
derivative `c · X v` (`hasDerivAt_dotProduct_mulVec_of_apply`).

This is variation of constants in block form, computed by one finite linear system.  Classically
the lower-left block is `∫₀ᵀ U(T, s) B(s) U(s, 0) ds`; the two-time propagator `U(T, s)` is not
constructed in the corpus, so that integral form is not stated here.

Scope.  The generator paths are continuous and the parameter enters affinely, as it does along a
segment of rate laws.  A general differentiable dependence on the parameter would need
differentiability uniform in time, which is not assumed.

## Empirical status

None.  The bodies here are integral identities and norm estimates for solutions of linear matrix
differential equations, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FundamentalMatrixParameterDerivative

open MeasureTheory LinearFundamentalMatrix IntegrableGeneratorPropagator IntegrableRateRealization
open scoped Matrix Matrix.Norms.Operator

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The block system -/

/-- **The lower-triangular block generator path** `[[P, 0], [C, D]]` over `ι ⊕ ι`. -/
def blockPath (P C D : ℝ → Matrix ι ι ℝ) (s : ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks (P s) 0 (C s) (D s)

/-- A block path of continuous blocks is continuous. -/
theorem continuous_blockPath {P C D : ℝ → Matrix ι ι ℝ} (hP : Continuous P) (hC : Continuous C)
    (hD : Continuous D) : Continuous (blockPath P C D) :=
  hP.matrix_fromBlocks continuous_const hC hD

/-- The upper-left block of a matrix over `ι ⊕ ι`, as a linear map. -/
def upperLeftBlock : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ →ₗ[ℝ] Matrix ι ι ℝ where
  toFun M := M.toBlocks₁₁
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The lower-left block of a matrix over `ι ⊕ ι`, as a linear map. -/
def lowerLeftBlock : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ →ₗ[ℝ] Matrix ι ι ℝ where
  toFun M := M.toBlocks₂₁
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The upper-left block of a sum is the sum of the upper-left blocks. -/
theorem toBlocks₁₁_add (M N : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    (M + N).toBlocks₁₁ = M.toBlocks₁₁ + N.toBlocks₁₁ :=
  rfl

/-- The lower-left block of a sum is the sum of the lower-left blocks. -/
theorem toBlocks₂₁_add (M N : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    (M + N).toBlocks₂₁ = M.toBlocks₂₁ + N.toBlocks₂₁ :=
  rfl

/-- The upper-left block of the identity is the identity. -/
theorem toBlocks₁₁_one : (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).toBlocks₁₁ = 1 := by
  rw [← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]

/-- The lower-left block of the identity is zero. -/
theorem toBlocks₂₁_one : (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).toBlocks₂₁ = 0 := by
  rw [← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₁]

/-- The upper-left block of an integral is the integral of the upper-left blocks. -/
theorem toBlocks₁₁_integral {f : ℝ → Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} (hf : Continuous f) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, f s).toBlocks₁₁ = ∫ s in (0 : ℝ)..t, (f s).toBlocks₁₁ :=
  ((LinearMap.toContinuousLinearMap (upperLeftBlock (ι := ι))).intervalIntegral_comp_comm
    (hf.intervalIntegrable 0 t)).symm

/-- The lower-left block of an integral is the integral of the lower-left blocks. -/
theorem toBlocks₂₁_integral {f : ℝ → Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} (hf : Continuous f) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, f s).toBlocks₂₁ = ∫ s in (0 : ℝ)..t, (f s).toBlocks₂₁ :=
  ((LinearMap.toContinuousLinearMap (lowerLeftBlock (ι := ι))).intervalIntegral_comp_comm
    (hf.intervalIntegrable 0 t)).symm

/-- The upper-left block of a block path times a matrix. -/
theorem toBlocks₁₁_blockPath_mul (P C D : ℝ → Matrix ι ι ℝ) (s : ℝ)
    (M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) : (blockPath P C D s * M).toBlocks₁₁ = P s * M.toBlocks₁₁ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  rw [blockPath, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, zero_mul, add_zero]

/-- The lower-left block of a block path times a matrix. -/
theorem toBlocks₂₁_blockPath_mul (P C D : ℝ → Matrix ι ι ℝ) (s : ℝ)
    (M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    (blockPath P C D s * M).toBlocks₂₁ = C s * M.toBlocks₁₁ + D s * M.toBlocks₂₁ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  rw [blockPath, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁]

/-- **The upper-left block of the block fundamental matrix** is the fundamental matrix of `P`. -/
theorem toBlocks₁₁_fundamentalMatrix_blockPath {P C D : ℝ → Matrix ι ι ℝ} (hP : Continuous P)
    (hC : Continuous C) (hD : Continuous D) {T : ℝ} (hT : 0 ≤ T) :
    ∀ t ∈ Set.Icc 0 T,
      (fundamentalMatrix (blockPath P C D) T t).toBlocks₁₁ = fundamentalMatrix P T t := by
  have hN := continuous_blockPath hP hC hD
  obtain ⟨K, hK, hbound⟩ := exists_bound_of_continuous hN hT
  obtain ⟨L, hL, hboundP⟩ := exists_bound_of_continuous hP hT
  have hΦ := continuous_fundamentalMatrix hN hT hK hbound
  have hV : Continuous fun t ↦ (fundamentalMatrix (blockPath P C D) T t).toBlocks₁₁ :=
    (LinearMap.continuous_of_finiteDimensional (upperLeftBlock (ι := ι))).comp hΦ
  have hVeq : ∀ t ∈ Set.Icc 0 T, (fundamentalMatrix (blockPath P C D) T t).toBlocks₁₁
      = 1 + ∫ s in (0 : ℝ)..t, P s * (fundamentalMatrix (blockPath P C D) T s).toBlocks₁₁ := by
    intro t ht
    rw [fundamentalMatrix_eq_integral hN hT hK hbound ht, toBlocks₁₁_add, toBlocks₁₁_one,
      toBlocks₁₁_integral (hN.mul hΦ) t]
    congr 1
    exact intervalIntegral.integral_congr fun s _ ↦ toBlocks₁₁_blockPath_mul P C D s _
  exact eq_of_integral_eq hT (hP.intervalIntegrable 0 T) hV
    (continuous_fundamentalMatrix hP hT hL hboundP) hVeq
    (fun t ht ↦ fundamentalMatrix_eq_integral hP hT hL hboundP ht)

/-- **The lower-left block of the block fundamental matrix solves the forced equation**
`X(t) = ∫₀ᵗ (C U_P + D X)`. -/
theorem toBlocks₂₁_fundamentalMatrix_blockPath_eq_integral {P C D : ℝ → Matrix ι ι ℝ}
    (hP : Continuous P) (hC : Continuous C) (hD : Continuous D) {T : ℝ} (hT : 0 ≤ T) :
    ∀ t ∈ Set.Icc 0 T, (fundamentalMatrix (blockPath P C D) T t).toBlocks₂₁
      = ∫ s in (0 : ℝ)..t, (C s * fundamentalMatrix P T s
          + D s * (fundamentalMatrix (blockPath P C D) T s).toBlocks₂₁) := by
  intro t ht
  have hN := continuous_blockPath hP hC hD
  obtain ⟨K, hK, hbound⟩ := exists_bound_of_continuous hN hT
  have hΦ := continuous_fundamentalMatrix hN hT hK hbound
  rw [fundamentalMatrix_eq_integral hN hT hK hbound ht, toBlocks₂₁_add, toBlocks₂₁_one, zero_add,
    toBlocks₂₁_integral (hN.mul hΦ) t]
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  have hsmem : s ∈ Set.Icc 0 T := by
    rw [Set.uIcc_of_le ht.1] at hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  rw [toBlocks₂₁_blockPath_mul, toBlocks₁₁_fundamentalMatrix_blockPath hP hC hD hT s hsmem]

/-! ## The exact difference along a line of paths -/

/-- **The exact difference.**  Along the line of paths `A + εB`, the fundamental matrix moves by
`ε` times the lower-left block of the fundamental matrix of `[[A + εB, 0], [B, A]]`. -/
theorem fundamentalMatrix_line_sub {A B : ℝ → Matrix ι ι ℝ} (hA : Continuous A)
    (hB : Continuous B) {T : ℝ} (hT : 0 ≤ T) (ε : ℝ) :
    ∀ t ∈ Set.Icc 0 T,
      fundamentalMatrix (fun s ↦ A s + ε • B s) T t - fundamentalMatrix A T t
        = ε • (fundamentalMatrix (blockPath (fun s ↦ A s + ε • B s) B A) T t).toBlocks₂₁ := by
  have hline : Continuous fun s ↦ A s + ε • B s := hA.add (continuous_const.smul hB)
  have hN := continuous_blockPath hline hB hA
  obtain ⟨K, hK, hboundLine⟩ := exists_bound_of_continuous hline hT
  obtain ⟨L, hL, hboundA⟩ := exists_bound_of_continuous hA hT
  obtain ⟨M, hM, hboundBlock⟩ := exists_bound_of_continuous hN hT
  have hU := continuous_fundamentalMatrix hline hT hK hboundLine
  have hX : Continuous fun t ↦
      (fundamentalMatrix (blockPath (fun s ↦ A s + ε • B s) B A) T t).toBlocks₂₁ :=
    (LinearMap.continuous_of_finiteDimensional (lowerLeftBlock (ι := ι))).comp
      (continuous_fundamentalMatrix hN hT hM hboundBlock)
  have hW : ∀ t ∈ Set.Icc 0 T,
      fundamentalMatrix (fun s ↦ A s + ε • B s) T t
          - ε • (fundamentalMatrix (blockPath (fun s ↦ A s + ε • B s) B A) T t).toBlocks₂₁
        = 1 + ∫ s in (0 : ℝ)..t, A s * (fundamentalMatrix (fun s ↦ A s + ε • B s) T s
          - ε • (fundamentalMatrix (blockPath (fun s ↦ A s + ε • B s) B A) T s).toBlocks₂₁) := by
    intro t ht
    have hf : IntervalIntegrable (fun s ↦ (A s + ε • B s)
        * fundamentalMatrix (fun s ↦ A s + ε • B s) T s) volume 0 t :=
      (hline.mul hU).intervalIntegrable 0 t
    have hg : IntervalIntegrable (fun s ↦ ε • (B s * fundamentalMatrix (fun s ↦ A s + ε • B s) T s
        + A s * (fundamentalMatrix (blockPath (fun s ↦ A s + ε • B s) B A) T s).toBlocks₂₁))
        volume 0 t :=
      (continuous_const.smul ((hB.mul hU).add (hA.mul hX))).intervalIntegrable 0 t
    calc fundamentalMatrix (fun s ↦ A s + ε • B s) T t
          - ε • (fundamentalMatrix (blockPath (fun s ↦ A s + ε • B s) B A) T t).toBlocks₂₁
        = (1 + ∫ s in (0 : ℝ)..t,
            (A s + ε • B s) * fundamentalMatrix (fun s ↦ A s + ε • B s) T s)
          - ε • ∫ s in (0 : ℝ)..t, (B s * fundamentalMatrix (fun s ↦ A s + ε • B s) T s
            + A s * (fundamentalMatrix (blockPath (fun s ↦ A s + ε • B s) B A) T s).toBlocks₂₁)
          := by
          rw [fundamentalMatrix_eq_integral hline hT hK hboundLine ht,
            toBlocks₂₁_fundamentalMatrix_blockPath_eq_integral hline hB hA hT t ht]
      _ = 1 + ∫ s in (0 : ℝ)..t,
            ((A s + ε • B s) * fundamentalMatrix (fun s ↦ A s + ε • B s) T s
              - ε • (B s * fundamentalMatrix (fun s ↦ A s + ε • B s) T s
                + A s * (fundamentalMatrix (blockPath (fun s ↦ A s + ε • B s) B A) T s).toBlocks₂₁))
          := by
          rw [intervalIntegral.integral_sub hf hg, intervalIntegral.integral_smul, add_sub_assoc]
      _ = 1 + ∫ s in (0 : ℝ)..t, A s * (fundamentalMatrix (fun s ↦ A s + ε • B s) T s
          - ε • (fundamentalMatrix (blockPath (fun s ↦ A s + ε • B s) B A) T s).toBlocks₂₁) := by
          congr 1
          refine intervalIntegral.integral_congr fun s _ ↦ ?_
          simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_add]
          abel
  intro t ht
  have heq : fundamentalMatrix (fun s ↦ A s + ε • B s) T t
      - ε • (fundamentalMatrix (blockPath (fun s ↦ A s + ε • B s) B A) T t).toBlocks₂₁
        = fundamentalMatrix A T t :=
    eq_of_integral_eq hT (hA.intervalIntegrable 0 T) (hU.sub (continuous_const.smul hX))
      (continuous_fundamentalMatrix hA hT hL hboundA) hW
      (fun t ht ↦ fundamentalMatrix_eq_integral hA hT hL hboundA ht) t ht
  rw [← heq]
  abel

/-! ## The limit -/

/-- **The block fundamental matrices converge along the line.**  For `|ε| ≤ 1`, the fundamental
matrices of `[[A + εB, 0], [B, A]]` and `[[A, 0], [B, A]]` at the horizon differ by at most
`|ε| K`. -/
theorem norm_fundamentalMatrix_blockLine_sub_le {A B : ℝ → Matrix ι ι ℝ} (hA : Continuous A)
    (hB : Continuous B) {T : ℝ} (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε ∈ Set.Icc (-1 : ℝ) 1,
      ‖fundamentalMatrix (blockPath (fun s ↦ A s + ε • B s) B A) T T
        - fundamentalMatrix (blockPath A B A) T T‖ ≤ |ε| * K := by
  have hN₀ := continuous_blockPath hA hB hA
  have hE := continuous_blockPath hB (continuous_const : Continuous fun _ : ℝ ↦ (0 : Matrix ι ι ℝ))
    (continuous_const : Continuous fun _ : ℝ ↦ (0 : Matrix ι ι ℝ))
  have hEint : 0 ≤ ∫ s in (0 : ℝ)..T, ‖blockPath B (fun _ ↦ 0) (fun _ ↦ 0) s‖ :=
    intervalIntegral.integral_nonneg hT fun s _ ↦ norm_nonneg _
  refine ⟨(∫ s in (0 : ℝ)..T, ‖blockPath B (fun _ ↦ 0) (fun _ ↦ 0) s‖)
      * Real.exp (∫ s in (0 : ℝ)..T, ‖blockPath A B A s‖)
      * Real.exp ((∫ s in (0 : ℝ)..T, ‖blockPath A B A s‖)
        + ∫ s in (0 : ℝ)..T, ‖blockPath B (fun _ ↦ 0) (fun _ ↦ 0) s‖),
    mul_nonneg (mul_nonneg hEint (Real.exp_pos _).le) (Real.exp_pos _).le, fun ε hε ↦ ?_⟩
  have hline : Continuous fun s ↦ A s + ε • B s := hA.add (continuous_const.smul hB)
  have hNε := continuous_blockPath hline hB hA
  have hdiff : ∀ s, blockPath (fun s ↦ A s + ε • B s) B A s - blockPath A B A s
      = ε • blockPath B (fun _ ↦ 0) (fun _ ↦ 0) s := by
    intro s
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [blockPath]
  have hnorm : ∀ s, ‖blockPath (fun s ↦ A s + ε • B s) B A s - blockPath A B A s‖
      = |ε| * ‖blockPath B (fun _ ↦ 0) (fun _ ↦ 0) s‖ := fun s ↦ by
    rw [hdiff, norm_smul, Real.norm_eq_abs]
  have habs : |ε| ≤ 1 := abs_le.mpr hε
  have hintegralDiff :
      ∫ s in (0 : ℝ)..T, ‖blockPath (fun s ↦ A s + ε • B s) B A s - blockPath A B A s‖
        = |ε| * ∫ s in (0 : ℝ)..T, ‖blockPath B (fun _ ↦ 0) (fun _ ↦ 0) s‖ := by
    simp only [hnorm]
    exact intervalIntegral.integral_const_mul _ _
  have hpoint : ∀ s, ‖blockPath (fun s ↦ A s + ε • B s) B A s‖
      ≤ ‖blockPath A B A s‖ + ‖blockPath B (fun _ ↦ 0) (fun _ ↦ 0) s‖ := by
    intro s
    have hsplit : blockPath (fun s ↦ A s + ε • B s) B A s
        = blockPath A B A s + ε • blockPath B (fun _ ↦ 0) (fun _ ↦ 0) s := by
      rw [← hdiff]
      abel
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) habs
  have hintegralNorm : ∫ s in (0 : ℝ)..T, ‖blockPath (fun s ↦ A s + ε • B s) B A s‖
      ≤ (∫ s in (0 : ℝ)..T, ‖blockPath A B A s‖)
        + ∫ s in (0 : ℝ)..T, ‖blockPath B (fun _ ↦ 0) (fun _ ↦ 0) s‖ := by
    calc ∫ s in (0 : ℝ)..T, ‖blockPath (fun s ↦ A s + ε • B s) B A s‖
        ≤ ∫ s in (0 : ℝ)..T,
            (‖blockPath A B A s‖ + ‖blockPath B (fun _ ↦ 0) (fun _ ↦ 0) s‖) :=
          intervalIntegral.integral_mono_on hT (hNε.norm.intervalIntegrable _ _)
            ((hN₀.norm.add hE.norm).intervalIntegrable _ _) fun s _ ↦ hpoint s
      _ = (∫ s in (0 : ℝ)..T, ‖blockPath A B A s‖)
          + ∫ s in (0 : ℝ)..T, ‖blockPath B (fun _ ↦ 0) (fun _ ↦ 0) s‖ :=
          intervalIntegral.integral_add (hN₀.norm.intervalIntegrable _ _)
            (hE.norm.intervalIntegrable _ _)
  have hbound := norm_fundamentalMatrix_sub_le_exp_integral hNε hN₀ hT T ⟨hT, le_rfl⟩
  rw [hintegralDiff] at hbound
  calc ‖fundamentalMatrix (blockPath (fun s ↦ A s + ε • B s) B A) T T
        - fundamentalMatrix (blockPath A B A) T T‖
      ≤ |ε| * (∫ s in (0 : ℝ)..T, ‖blockPath B (fun _ ↦ 0) (fun _ ↦ 0) s‖)
          * Real.exp (∫ s in (0 : ℝ)..T, ‖blockPath A B A s‖)
          * Real.exp (∫ s in (0 : ℝ)..T, ‖blockPath (fun s ↦ A s + ε • B s) B A s‖) := hbound
    _ ≤ |ε| * (∫ s in (0 : ℝ)..T, ‖blockPath B (fun _ ↦ 0) (fun _ ↦ 0) s‖)
          * Real.exp (∫ s in (0 : ℝ)..T, ‖blockPath A B A s‖)
          * Real.exp ((∫ s in (0 : ℝ)..T, ‖blockPath A B A s‖)
            + ∫ s in (0 : ℝ)..T, ‖blockPath B (fun _ ↦ 0) (fun _ ↦ 0) s‖) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hintegralNorm)
          (mul_nonneg (mul_nonneg (abs_nonneg _) hEint) (Real.exp_pos _).le)
    _ = |ε| * ((∫ s in (0 : ℝ)..T, ‖blockPath B (fun _ ↦ 0) (fun _ ↦ 0) s‖)
          * Real.exp (∫ s in (0 : ℝ)..T, ‖blockPath A B A s‖)
          * Real.exp ((∫ s in (0 : ℝ)..T, ‖blockPath A B A s‖)
            + ∫ s in (0 : ℝ)..T, ‖blockPath B (fun _ ↦ 0) (fun _ ↦ 0) s‖)) := by
        ring

/-- The entry `(i, j)` of the lower-left block, as a continuous linear functional. -/
def lowerLeftEntry (i j : ι) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M ↦ M.toBlocks₂₁ i j, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }

/-- **The derivative along a line of paths.**  Every entry of `ε ↦ U_{A+εB}(T)` has as derivative
at `0` the corresponding entry of the lower-left block of the fundamental matrix of
`[[A, 0], [B, A]]`. -/
theorem hasDerivAt_fundamentalMatrix_line {A B : ℝ → Matrix ι ι ℝ} (hA : Continuous A)
    (hB : Continuous B) {T : ℝ} (hT : 0 ≤ T) (i j : ι) :
    HasDerivAt (fun ε : ℝ ↦ fundamentalMatrix (fun s ↦ A s + ε • B s) T T i j)
      ((fundamentalMatrix (blockPath A B A) T T).toBlocks₂₁ i j) (0 : ℝ) := by
  obtain ⟨K, hK, hbound⟩ := norm_fundamentalMatrix_blockLine_sub_le hA hB hT
  have hsmall : Filter.Tendsto (fun ε : ℝ ↦ ‖lowerLeftEntry (ι := ι) i j‖ * (|ε| * K))
      (nhds 0) (nhds 0) := by
    have hcont : Continuous fun ε : ℝ ↦ ‖lowerLeftEntry (ι := ι) i j‖ * (|ε| * K) :=
      continuous_const.mul (continuous_abs.mul continuous_const)
    simpa using hcont.tendsto 0
  have hlimit : Filter.Tendsto
      (fun ε : ℝ ↦
        (fundamentalMatrix (blockPath (fun s ↦ A s + ε • B s) B A) T T).toBlocks₂₁ i j)
      (nhds (0 : ℝ)) (nhds ((fundamentalMatrix (blockPath A B A) T T).toBlocks₂₁ i j)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hsmall
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)]
      with ε hε
    have hentry := (lowerLeftEntry (ι := ι) i j).le_opNorm
      (fundamentalMatrix (blockPath (fun s ↦ A s + ε • B s) B A) T T
        - fundamentalMatrix (blockPath A B A) T T)
    rw [map_sub] at hentry
    exact hentry.trans (mul_le_mul_of_nonneg_left (hbound ε ⟨hε.1.le, hε.2.le⟩) (norm_nonneg _))
  have hzero : (fun s ↦ A s + (0 : ℝ) • B s) = A := funext fun s ↦ by rw [zero_smul, add_zero]
  rw [hasDerivAt_iff_tendsto_slope]
  refine (hlimit.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hne : ε ≠ 0 := hε
  have hsub := congrFun (congrFun (fundamentalMatrix_line_sub hA hB hT ε T ⟨hT, le_rfl⟩) i) j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hsub
  simp only [slope_def_field, sub_zero, hzero, hsub, mul_div_cancel_left₀ _ hne]

/-- **The derivative of a fundamental matrix along an affine family of paths.**  Every entry of
`θ ↦ U_{A+θB}(T)` has as derivative at `θ₀` the corresponding entry of the lower-left block of the
fundamental matrix of `[[A + θ₀B, 0], [B, A + θ₀B]]`. -/
theorem hasDerivAt_fundamentalMatrix_affinePath {A B : ℝ → Matrix ι ι ℝ} (hA : Continuous A)
    (hB : Continuous B) {T : ℝ} (hT : 0 ≤ T) (θ₀ : ℝ) (i j : ι) :
    HasDerivAt (fun θ ↦ fundamentalMatrix (fun s ↦ A s + θ • B s) T T i j)
      ((fundamentalMatrix
        (blockPath (fun s ↦ A s + θ₀ • B s) B (fun s ↦ A s + θ₀ • B s)) T T).toBlocks₂₁ i j)
      θ₀ := by
  have hbase : Continuous fun s ↦ A s + θ₀ • B s := hA.add (continuous_const.smul hB)
  have h0 := hasDerivAt_fundamentalMatrix_line hbase hB hT i j
  have hshift := HasDerivAt.comp_sub_const θ₀ θ₀ (by rwa [sub_self])
    (f := fun ε ↦ fundamentalMatrix (fun s ↦ (A s + θ₀ • B s) + ε • B s) T T i j)
  refine hshift.congr_of_eventuallyEq (Filter.Eventually.of_forall fun θ ↦ ?_)
  have hpath : (fun s ↦ A s + θ • B s) = fun s ↦ (A s + θ₀ • B s) + (θ - θ₀) • B s :=
    funext fun s ↦ by
      rw [sub_smul]
      abel
  rw [hpath]

/-- **Pairing an entrywise derivative.**  If every entry of a matrix path has a derivative, then
`c · M v` has derivative `c · M' v`. -/
theorem hasDerivAt_dotProduct_mulVec_of_apply {M : ℝ → Matrix ι ι ℝ} {M' : Matrix ι ι ℝ}
    {θ₀ : ℝ} (hM : ∀ i j, HasDerivAt (fun θ ↦ M θ i j) (M' i j) θ₀) (c v : ι → ℝ) :
    HasDerivAt (fun θ ↦ c ⬝ᵥ (M θ *ᵥ v)) (c ⬝ᵥ (M' *ᵥ v)) θ₀ := by
  have hsum : HasDerivAt (fun θ ↦ ∑ i, c i * ∑ j, M θ i j * v j)
      (∑ i, c i * ∑ j, M' i j * v j) θ₀ :=
    HasDerivAt.fun_sum fun i _ ↦
      (HasDerivAt.fun_sum fun j _ ↦ (hM i j).mul_const (v j)).const_mul (c i)
  exact hsum

end

end Descent.Portability.FundamentalMatrixParameterDerivative
