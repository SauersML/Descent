/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndSensitivityRatePath
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

assert_below Descent.Decision Descent.Program

/-!
# The two-time propagator of a time-varying generator path

`LinearFundamentalMatrix` constructs the fundamental matrix `U(t)` of `U' = A(t) U`, `U(0) = 1`,
for a continuous generator path.  `FundamentalMatrixParameterDerivative` differentiates it along an
affine family of paths, in block form.  This module constructs the two-time propagator `U(t, s)`
and writes that derivative as the variation-of-constants integral.

The inverse.  The transposed path `s ↦ -(A s)ᵀ` has a fundamental matrix, and its transpose `V`
(`adjointFundamentalMatrix`) solves `V' = -V A`, `V(0) = 1`
(`hasDerivWithinAt_adjointFundamentalMatrix`).  So `V U` has derivative zero on the horizon and is
the identity there (`adjointFundamentalMatrix_mul_fundamentalMatrix`).  A one-sided inverse of a
square matrix is two-sided, so `U V` is the identity as well
(`fundamentalMatrix_mul_adjointFundamentalMatrix`).

The propagator.  `U(t, s) = U(t) V(s)` (`twoTimePropagator`) has these properties:
- it is the identity on the diagonal of the horizon (`twoTimePropagator_self`);
- it obeys Chapman–Kolmogorov, `U(t, s) U(s, r) = U(t, r)` (`twoTimePropagator_mul`);
- from the start of the horizon it is the fundamental matrix (`twoTimePropagator_zero_right`), in
  particular the dual propagator of a rate history (`twoTimePropagator_rateHistory`);
- it solves the forward equation `∂ₜ U(t, s) = A(t) U(t, s)`
  (`hasDerivWithinAt_twoTimePropagator_left`) and the backward equation
  `∂ₛ U(t, s) = -U(t, s) A(s)` (`hasDerivWithinAt_twoTimePropagator_right`) on the horizon.

The Duhamel identity.  For continuous `P` and `C`, the lower-left block `X` of the fundamental
matrix of `[[P, 0], [C, P]]` is `∫₀ᵗ U_P(t, s) C(s) U_P(s, 0) ds`
(`toBlocks₂₁_fundamentalMatrix_blockPath_eq_integral_twoTimePropagator`).  The product `V X` has
derivative `V C U`, so `X(t) = U(t) ∫₀ᵗ V C U`.  Along an affine path `A + θ B`, every entry of
`U_θ(T, 0)` therefore has as derivative at `θ₀` the corresponding entry of
`∫₀ᵀ U_θ₀(T, s) B(s) U_θ₀(s, 0) ds` (`hasDerivAt_twoTimePropagator_affinePath`).  The sensitivity
matrix of a segment of rate histories is that integral with `B = Q_second - Q_first`
(`ratePathSensitivity_eq_integral`).

Significance.  The block form of `EndToEndSensitivityRatePath` computes the sensitivity with one
finite linear system.  The integral form shows where it comes from.  A perturbation `Δ(s)` of the
generator at time `s` acts on the moments propagated from `0` to `s`, and the result is carried
from `s` to `T` by the unperturbed two-time propagator.

Scope.  The generator paths are continuous on the line, as the fundamental matrices of the corpus
require.  The derivatives in `t` and in `s` are stated within the horizon `[0, T]`, and
invertibility of `U(t)` is proved on the horizon, where the construction solves its equation.

## Empirical status

None.  The bodies here are derivatives and integrals of solutions of linear matrix differential
equations and finite-dimensional matrix algebra, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.TwoTimeRatePropagator

open MeasureTheory LinearFundamentalMatrix IntegrableGeneratorPropagator
  FundamentalMatrixParameterDerivative
open scoped Matrix Matrix.Norms.Operator

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Linear maps of matrices -/

/-- Transposition of square matrices, as a continuous linear map. -/
def transposeMap : Matrix ι ι ℝ →L[ℝ] Matrix ι ι ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M ↦ Mᵀ, map_add' := Matrix.transpose_add, map_smul' := Matrix.transpose_smul }

/-- Left multiplication by a fixed square matrix, as a continuous linear map. -/
def mulLeftMap (M : Matrix ι ι ℝ) : Matrix ι ι ℝ →L[ℝ] Matrix ι ι ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun N ↦ M * N, map_add' := mul_add M, map_smul' := fun c N ↦ mul_smul_comm c M N }

/-- A matrix path with derivative zero within the horizon is constant on the horizon. -/
theorem eq_of_hasDerivWithinAt_zero {f : ℝ → Matrix ι ι ℝ} {T : ℝ}
    (hderiv : ∀ s ∈ Set.Icc 0 T, HasDerivWithinAt f 0 (Set.Icc 0 T) s) :
    ∀ t ∈ Set.Icc 0 T, f t = f 0 := by
  intro t ht
  have hbound := norm_image_sub_le_of_norm_deriv_le_segment' hderiv
    (fun _ _ ↦ (norm_zero : ‖(0 : Matrix ι ι ℝ)‖ = 0).le) t ht
  rw [zero_mul] at hbound
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hbound)

/-! ## The adjoint fundamental matrix -/

/-- The transposed generator path `s ↦ -(A s)ᵀ` of a continuous path is continuous. -/
theorem continuous_neg_transpose {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A) :
    Continuous fun s ↦ -(A s)ᵀ :=
  ((transposeMap (ι := ι)).continuous.comp hA).neg

/-- **The adjoint fundamental matrix**: the transpose of the fundamental matrix of the transposed
path `s ↦ -(A s)ᵀ`. -/
def adjointFundamentalMatrix (A : ℝ → Matrix ι ι ℝ) (T t : ℝ) : Matrix ι ι ℝ :=
  (fundamentalMatrix (fun s ↦ -(A s)ᵀ) T t)ᵀ

/-- The adjoint fundamental matrix starts at the identity. -/
theorem adjointFundamentalMatrix_zero (A : ℝ → Matrix ι ι ℝ) {T : ℝ} (hT : 0 ≤ T) :
    adjointFundamentalMatrix A T 0 = 1 := by
  rw [adjointFundamentalMatrix, fundamentalMatrix_zero _ hT, Matrix.transpose_one]

/-- The adjoint fundamental matrix of a continuous path is continuous. -/
theorem continuous_adjointFundamentalMatrix {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A) {T : ℝ}
    (hT : 0 ≤ T) : Continuous (adjointFundamentalMatrix A T) := by
  obtain ⟨K, hK, hbound⟩ := exists_bound_of_continuous (continuous_neg_transpose hA) hT
  exact (transposeMap (ι := ι)).continuous.comp
    (continuous_fundamentalMatrix (continuous_neg_transpose hA) hT hK hbound)

/-- **The adjoint equation.**  On the horizon the adjoint fundamental matrix solves
`V' = -V A`. -/
theorem hasDerivWithinAt_adjointFundamentalMatrix {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A)
    {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    HasDerivWithinAt (adjointFundamentalMatrix A T) (-(adjointFundamentalMatrix A T t * A t))
      (Set.Icc 0 T) t := by
  obtain ⟨K, hK, hbound⟩ := exists_bound_of_continuous (continuous_neg_transpose hA) hT
  have hW := fundamentalMatrix_hasDerivWithinAt (continuous_neg_transpose hA) hT hK hbound ht
  have htransposed : HasDerivWithinAt (adjointFundamentalMatrix A T)
      ((-(A t)ᵀ * fundamentalMatrix (fun s ↦ -(A s)ᵀ) T t)ᵀ) (Set.Icc 0 T) t :=
    HasFDerivAt.comp_hasDerivWithinAt (hl := (transposeMap (ι := ι)).hasFDerivAt) (hf := hW)
  refine htransposed.congr_deriv ?_
  simp only [adjointFundamentalMatrix, Matrix.transpose_mul, Matrix.transpose_neg,
    Matrix.transpose_transpose, mul_neg]

/-- **The adjoint fundamental matrix is a left inverse of the fundamental matrix** on the
horizon. -/
theorem adjointFundamentalMatrix_mul_fundamentalMatrix {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A)
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ t ∈ Set.Icc 0 T, adjointFundamentalMatrix A T t * fundamentalMatrix A T t = 1 := by
  obtain ⟨K, hK, hbound⟩ := exists_bound_of_continuous hA hT
  have hderiv : ∀ s ∈ Set.Icc 0 T, HasDerivWithinAt
      (fun u ↦ adjointFundamentalMatrix A T u * fundamentalMatrix A T u) 0 (Set.Icc 0 T) s := by
    intro s hs
    refine ((hasDerivWithinAt_adjointFundamentalMatrix hA hT hs).fun_mul
      (fundamentalMatrix_hasDerivWithinAt hA hT hK hbound hs)).congr_deriv ?_
    noncomm_ring
  intro t ht
  rw [eq_of_hasDerivWithinAt_zero hderiv t ht, adjointFundamentalMatrix_zero A hT,
    fundamentalMatrix_zero A hT, one_mul]

/-- **The fundamental matrix is invertible on the horizon**, with the adjoint fundamental matrix
as its inverse. -/
theorem fundamentalMatrix_mul_adjointFundamentalMatrix {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A)
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ t ∈ Set.Icc 0 T, fundamentalMatrix A T t * adjointFundamentalMatrix A T t = 1 :=
  fun t ht ↦ Matrix.mul_eq_one_comm.mp (adjointFundamentalMatrix_mul_fundamentalMatrix hA hT t ht)

/-! ## The two-time propagator -/

/-- **The two-time propagator** `U(t, s) = U(t) V(s)` of a generator path over the horizon
`[0, T]`. -/
def twoTimePropagator (A : ℝ → Matrix ι ι ℝ) (T t s : ℝ) : Matrix ι ι ℝ :=
  fundamentalMatrix A T t * adjointFundamentalMatrix A T s

/-- The two-time propagator is the identity on the diagonal of the horizon. -/
theorem twoTimePropagator_self {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A) {T : ℝ} (hT : 0 ≤ T)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) : twoTimePropagator A T t t = 1 := by
  rw [twoTimePropagator, fundamentalMatrix_mul_adjointFundamentalMatrix hA hT t ht]

/-- **Chapman–Kolmogorov.**  For an intermediate time on the horizon,
`U(t, s) U(s, r) = U(t, r)`. -/
theorem twoTimePropagator_mul {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A) {T : ℝ} (hT : 0 ≤ T)
    {s : ℝ} (hs : s ∈ Set.Icc 0 T) (t r : ℝ) :
    twoTimePropagator A T t s * twoTimePropagator A T s r = twoTimePropagator A T t r := by
  simp only [twoTimePropagator]
  rw [mul_assoc, ← mul_assoc (adjointFundamentalMatrix A T s),
    adjointFundamentalMatrix_mul_fundamentalMatrix hA hT s hs, one_mul]

/-- From the start of the horizon the two-time propagator is the fundamental matrix. -/
theorem twoTimePropagator_zero_right (A : ℝ → Matrix ι ι ℝ) {T : ℝ} (hT : 0 ≤ T) (t : ℝ) :
    twoTimePropagator A T t 0 = fundamentalMatrix A T t := by
  rw [twoTimePropagator, adjointFundamentalMatrix_zero A hT, mul_one]

/-- **The forward equation.**  On the horizon `∂ₜ U(t, s) = A(t) U(t, s)`. -/
theorem hasDerivWithinAt_twoTimePropagator_left {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A)
    {T : ℝ} (hT : 0 ≤ T) (s : ℝ) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    HasDerivWithinAt (fun u ↦ twoTimePropagator A T u s) (A t * twoTimePropagator A T t s)
      (Set.Icc 0 T) t := by
  obtain ⟨K, hK, hbound⟩ := exists_bound_of_continuous hA hT
  refine ((fundamentalMatrix_hasDerivWithinAt hA hT hK hbound ht).fun_mul
    (hasDerivWithinAt_const t (Set.Icc 0 T) (adjointFundamentalMatrix A T s))).congr_deriv ?_
  simp only [mul_zero, add_zero, twoTimePropagator, mul_assoc]

/-- **The backward equation.**  On the horizon `∂ₛ U(t, s) = -U(t, s) A(s)`. -/
theorem hasDerivWithinAt_twoTimePropagator_right {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A)
    {T : ℝ} (hT : 0 ≤ T) (t : ℝ) {s : ℝ} (hs : s ∈ Set.Icc 0 T) :
    HasDerivWithinAt (fun u ↦ twoTimePropagator A T t u) (-(twoTimePropagator A T t s * A s))
      (Set.Icc 0 T) s := by
  refine ((hasDerivWithinAt_const s (Set.Icc 0 T) (fundamentalMatrix A T t)).fun_mul
    (hasDerivWithinAt_adjointFundamentalMatrix hA hT hs)).congr_deriv ?_
  simp only [zero_mul, zero_add, twoTimePropagator, mul_neg, mul_assoc]

/-! ## The Duhamel identity -/

/-- The lower-left block of the fundamental matrix of `[[P, 0], [C, P]]` has derivative
`C U_P + P X` on the horizon. -/
theorem hasDerivWithinAt_toBlocks₂₁_fundamentalMatrix_blockPath {P C : ℝ → Matrix ι ι ℝ}
    (hP : Continuous P) (hC : Continuous C) {T : ℝ} (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) :
    HasDerivWithinAt (fun u ↦ (fundamentalMatrix (blockPath P C P) T u).toBlocks₂₁)
      (C t * fundamentalMatrix P T t + P t * (fundamentalMatrix (blockPath P C P) T t).toBlocks₂₁)
      (Set.Icc 0 T) t := by
  have hN := continuous_blockPath hP hC hP
  obtain ⟨K, hK, hbound⟩ := exists_bound_of_continuous hN hT
  obtain ⟨L, hL, hboundP⟩ := exists_bound_of_continuous hP hT
  have hX : Continuous fun u ↦ (fundamentalMatrix (blockPath P C P) T u).toBlocks₂₁ :=
    (LinearMap.continuous_of_finiteDimensional (lowerLeftBlock (ι := ι))).comp
      (continuous_fundamentalMatrix hN hT hK hbound)
  have hforce : Continuous fun u ↦ C u * fundamentalMatrix P T u
      + P u * (fundamentalMatrix (blockPath P C P) T u).toBlocks₂₁ :=
    (hC.mul (continuous_fundamentalMatrix hP hT hL hboundP)).add (hP.mul hX)
  have hprimitive : HasDerivAt (fun u ↦ ∫ r in (0 : ℝ)..u, (C r * fundamentalMatrix P T r
        + P r * (fundamentalMatrix (blockPath P C P) T r).toBlocks₂₁))
      (C t * fundamentalMatrix P T t + P t * (fundamentalMatrix (blockPath P C P) T t).toBlocks₂₁)
      t :=
    intervalIntegral.integral_hasDerivAt_right (hforce.intervalIntegrable 0 t)
      (hforce.stronglyMeasurableAtFilter _ _) hforce.continuousAt
  exact hprimitive.hasDerivWithinAt.congr
    (fun r hr ↦ toBlocks₂₁_fundamentalMatrix_blockPath_eq_integral hP hC hP hT r hr)
    (toBlocks₂₁_fundamentalMatrix_blockPath_eq_integral hP hC hP hT t ht)

/-- **The Duhamel identity in block form.**  For continuous `P` and `C`, on the horizon the
lower-left block of the fundamental matrix of `[[P, 0], [C, P]]` is
`∫₀ᵗ U_P(t, s) C(s) U_P(s, 0) ds`. -/
theorem toBlocks₂₁_fundamentalMatrix_blockPath_eq_integral_twoTimePropagator
    {P C : ℝ → Matrix ι ι ℝ} (hP : Continuous P) (hC : Continuous C) {T : ℝ} (hT : 0 ≤ T) :
    ∀ t ∈ Set.Icc 0 T, (fundamentalMatrix (blockPath P C P) T t).toBlocks₂₁
      = ∫ s in (0 : ℝ)..t, twoTimePropagator P T t s * C s * twoTimePropagator P T s 0 := by
  obtain ⟨L, hL, hboundP⟩ := exists_bound_of_continuous hP hT
  have hU := continuous_fundamentalMatrix hP hT hL hboundP
  have hsource : Continuous fun s ↦
      adjointFundamentalMatrix P T s * C s * fundamentalMatrix P T s :=
    ((continuous_adjointFundamentalMatrix hP hT).mul hC).mul hU
  have hderiv : ∀ s ∈ Set.Icc 0 T, HasDerivWithinAt
      (fun u ↦ adjointFundamentalMatrix P T u * (fundamentalMatrix (blockPath P C P) T u).toBlocks₂₁
        - ∫ r in (0 : ℝ)..u, adjointFundamentalMatrix P T r * C r * fundamentalMatrix P T r)
      0 (Set.Icc 0 T) s := by
    intro s hs
    have hprimitive : HasDerivAt
        (fun u ↦ ∫ r in (0 : ℝ)..u, adjointFundamentalMatrix P T r * C r * fundamentalMatrix P T r)
        (adjointFundamentalMatrix P T s * C s * fundamentalMatrix P T s) s :=
      intervalIntegral.integral_hasDerivAt_right (hsource.intervalIntegrable 0 s)
        (hsource.stronglyMeasurableAtFilter _ _) hsource.continuousAt
    refine (((hasDerivWithinAt_adjointFundamentalMatrix hP hT hs).fun_mul
      (hasDerivWithinAt_toBlocks₂₁_fundamentalMatrix_blockPath hP hC hT hs)).sub
        hprimitive.hasDerivWithinAt).congr_deriv ?_
    noncomm_ring
  intro t ht
  have hinitial :
      adjointFundamentalMatrix P T 0 * (fundamentalMatrix (blockPath P C P) T 0).toBlocks₂₁
      - ∫ r in (0 : ℝ)..0, adjointFundamentalMatrix P T r * C r * fundamentalMatrix P T r = 0 := by
    rw [fundamentalMatrix_zero _ hT, toBlocks₂₁_one, mul_zero, intervalIntegral.integral_same,
      sub_zero]
  have hpropagated :
      adjointFundamentalMatrix P T t * (fundamentalMatrix (blockPath P C P) T t).toBlocks₂₁
        = ∫ r in (0 : ℝ)..t, adjointFundamentalMatrix P T r * C r * fundamentalMatrix P T r :=
    sub_eq_zero.mp ((eq_of_hasDerivWithinAt_zero hderiv t ht).trans hinitial)
  have hpull : ∫ s in (0 : ℝ)..t,
        fundamentalMatrix P T t * (adjointFundamentalMatrix P T s * C s * fundamentalMatrix P T s)
      = fundamentalMatrix P T t
        * ∫ s in (0 : ℝ)..t, adjointFundamentalMatrix P T s * C s * fundamentalMatrix P T s :=
    (mulLeftMap (fundamentalMatrix P T t)).intervalIntegral_comp_comm
      (hsource.intervalIntegrable 0 t)
  calc (fundamentalMatrix (blockPath P C P) T t).toBlocks₂₁
      = fundamentalMatrix P T t * adjointFundamentalMatrix P T t
          * (fundamentalMatrix (blockPath P C P) T t).toBlocks₂₁ := by
        rw [fundamentalMatrix_mul_adjointFundamentalMatrix hP hT t ht, one_mul]
    _ = fundamentalMatrix P T t
          * ∫ s in (0 : ℝ)..t, adjointFundamentalMatrix P T s * C s * fundamentalMatrix P T s := by
        rw [mul_assoc, hpropagated]
    _ = ∫ s in (0 : ℝ)..t, twoTimePropagator P T t s * C s * twoTimePropagator P T s 0 := by
        rw [← hpull]
        refine intervalIntegral.integral_congr fun s _ ↦ ?_
        simp only [twoTimePropagator, adjointFundamentalMatrix_zero P hT, mul_one, mul_assoc]

/-- **The Duhamel derivative along an affine family of paths.**  Every entry of
`θ ↦ U_{A+θB}(T, 0)` has as derivative at `θ₀` the corresponding entry of
`∫₀ᵀ U_θ₀(T, s) B(s) U_θ₀(s, 0) ds`, with `U_θ₀` the two-time propagator of `A + θ₀ B`. -/
theorem hasDerivAt_twoTimePropagator_affinePath {A B : ℝ → Matrix ι ι ℝ} (hA : Continuous A)
    (hB : Continuous B) {T : ℝ} (hT : 0 ≤ T) (θ₀ : ℝ) (i j : ι) :
    HasDerivAt (fun θ ↦ twoTimePropagator (fun s ↦ A s + θ • B s) T T 0 i j)
      ((∫ s in (0 : ℝ)..T, twoTimePropagator (fun s ↦ A s + θ₀ • B s) T T s * B s
        * twoTimePropagator (fun s ↦ A s + θ₀ • B s) T s 0) i j) θ₀ := by
  have hbase : Continuous fun s ↦ A s + θ₀ • B s := hA.add (continuous_const.smul hB)
  rw [← toBlocks₂₁_fundamentalMatrix_blockPath_eq_integral_twoTimePropagator hbase hB hT T
    ⟨hT, le_rfl⟩]
  refine (hasDerivAt_fundamentalMatrix_affinePath hA hB hT θ₀ i j).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun θ ↦ ?_)
  simp only [twoTimePropagator_zero_right _ hT]

/-! ## Rate histories -/

section RateHistory

open PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
  NeutralRateHistoryRealization EndToEndSensitivityRates EndToEndSensitivityRatePath

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-- **The two-time propagator of a rate history from the start of the horizon is its dual
propagator.** -/
theorem twoTimePropagator_rateHistory (rates : ℝ → NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    twoTimePropagator (dualGeneratorPath rates capacity T) T T 0
      = rateHistoryDualPropagator rates capacity T :=
  twoTimePropagator_zero_right _ hT T

/-- **The sensitivity matrix of a segment of rate histories in integral form.**  It is
`∫₀ᵀ U_θ₀(T, s) (Q_second - Q_first)(s) U_θ₀(s, 0) ds`, with `U_θ₀` the two-time propagator of the
dual generator path `Q_first + θ₀ (Q_second - Q_first)`. -/
theorem ratePathSensitivity_eq_integral {first second : ℝ → NeutralRates Deme Locus Allele}
    {capacity : Locus → ℕ} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (θ₀ : ℝ) :
    ratePathSensitivity first second capacity T θ₀
      = ∫ s in (0 : ℝ)..T, twoTimePropagator (fun s ↦ dualGeneratorPath first capacity T s
          + θ₀ • (dualGeneratorPath second capacity T s - dualGeneratorPath first capacity T s))
          T T s
        * (dualGeneratorPath second capacity T s - dualGeneratorPath first capacity T s)
        * twoTimePropagator (fun s ↦ dualGeneratorPath first capacity T s
          + θ₀ • (dualGeneratorPath second capacity T s - dualGeneratorPath first capacity T s))
          T s 0 := by
  have hA := continuous_dualGeneratorPath hT hfirst
  have hB := (continuous_dualGeneratorPath hT hsecond).sub hA
  have hP : Continuous fun s ↦ dualGeneratorPath first capacity T s
      + θ₀ • (dualGeneratorPath second capacity T s - dualGeneratorPath first capacity T s) :=
    hA.add (continuous_const.smul hB)
  have hC : Continuous fun s ↦
      dualGeneratorPath second capacity T s - dualGeneratorPath first capacity T s := hB
  exact toBlocks₂₁_fundamentalMatrix_blockPath_eq_integral_twoTimePropagator hP hC hT T
    ⟨hT, le_rfl⟩

end RateHistory

end

end Descent.Portability.TwoTimeRatePropagator
