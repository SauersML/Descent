/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteMetricIdentification
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.LinearIndependent.Basic

assert_below Descent.Decision Descent.Program

/-!
Finite covariance families admit a single separating projection. Along that
projection the Gaussian characteristic functions reduce to distinct exponential
characters. The character independence is Dedekind's classical theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianCovarianceSeparation

open scoped BigOperators

variable {I D : Type*} [Fintype I] [Fintype D]

omit [Fintype D] in
theorem exists_separating_evaluation (p : I → MvPolynomial D ℝ)
    (hp : Function.Injective p) :
    ∃ v : D → ℝ, Function.Injective (fun i ↦ MvPolynomial.eval v (p i)) := by
  classical
  let pairs := {ij : I × I // ij.1 ≠ ij.2}
  let product : MvPolynomial D ℝ := ∏ ij : pairs, (p ij.val.1 - p ij.val.2)
  have hproduct : product ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro ij _
    exact sub_ne_zero.mpr (fun h ↦ ij.property (hp h))
  have hex : ∃ v : D → ℝ, MvPolynomial.eval v product ≠ 0 := by
    by_contra h
    push_neg at h
    apply hproduct
    apply MvPolynomial.funext
    intro v
    simpa using h v
  obtain ⟨v, hv⟩ := hex
  refine ⟨v, fun i j hij ↦ ?_⟩
  by_contra hne
  have hn := Finset.prod_ne_zero_iff.mp (show (∏ ij : pairs,
      MvPolynomial.eval v (p ij.val.1 - p ij.val.2)) ≠ 0 by
    simpa only [product, map_prod] using hv) ⟨(i, j), hne⟩ (Finset.mem_univ _)
  apply hn
  simp only [map_sub, hij, sub_self]

noncomputable def covariancePolynomial (A : Matrix D D ℝ) : MvPolynomial D ℝ :=
  ∑ i, ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X i * MvPolynomial.X j

noncomputable def quadraticValue (A : Matrix D D ℝ) (v : D → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * v i * v j

theorem eval_covariancePolynomial (A : Matrix D D ℝ) (v : D → ℝ) :
    MvPolynomial.eval v (covariancePolynomial A) = quadraticValue A v := by
  simp [covariancePolynomial, quadraticValue]

theorem quadraticValue_single [DecidableEq D] (A : Matrix D D ℝ) (i : D) :
    quadraticValue A (Pi.single i 1) = A i i := by
  simp [quadraticValue, Pi.single_apply]

theorem quadraticValue_pair [DecidableEq D] (A : Matrix D D ℝ) (i j : D) :
    quadraticValue A (Pi.single i 1 + Pi.single j 1) = A i i + A i j + A j i + A j j := by
  simp [quadraticValue, Pi.single_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem covariancePolynomial_injective (A B : Matrix D D ℝ)
    (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i)
    (h : covariancePolynomial A = covariancePolynomial B) : A = B := by
  classical
  have he (v : D → ℝ) : quadraticValue A v = quadraticValue B v := by
    simpa only [eval_covariancePolynomial] using congrArg (MvPolynomial.eval v) h
  have hd (i : D) : A i i = B i i := by
    simpa only [quadraticValue_single] using he (Pi.single i 1)
  ext i j
  have hh := he (Pi.single i 1 + Pi.single j 1)
  rw [quadraticValue_pair, quadraticValue_pair, hA j i, hB j i, hd i, hd j] at hh
  linarith

theorem exists_covariance_separating_vector (A : I → Matrix D D ℝ)
    (hs : ∀ k i j, A k i j = A k j i) (hA : Function.Injective A) :
    ∃ v : D → ℝ, Function.Injective (fun k ↦ quadraticValue (A k) v) := by
  have hp : Function.Injective (fun k ↦ covariancePolynomial (A k)) := by
    intro i j h
    exact hA (covariancePolynomial_injective (A i) (A j) (hs i) (hs j) h)
  simpa only [eval_covariancePolynomial] using exists_separating_evaluation _ hp

theorem quadraticValue_smul (A : Matrix D D ℝ) (c : ℝ) (v : D → ℝ) :
    quadraticValue A (c • v) = c ^ 2 * quadraticValue A v := by
  simp only [quadraticValue, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

noncomputable def exponentialCharacter (rate : ℝ) : Multiplicative NNReal →* ℝ where
  toFun t := Real.exp (rate * ((Multiplicative.toAdd t : NNReal) : ℝ))
  map_one' := by simp
  map_mul' s t := by simp [mul_add, Real.exp_add]

theorem exponentialCharacter_injective : Function.Injective exponentialCharacter := by
  intro a b h
  have hh := congrArg (fun f : Multiplicative NNReal →* ℝ ↦ f (Multiplicative.ofAdd 1)) h
  simpa [exponentialCharacter] using hh

omit [Fintype I] in
theorem exponential_characters_independent (rate : I → ℝ) (hrate : Function.Injective rate) :
    LinearIndependent ℝ (fun i ↦ (exponentialCharacter (rate i) : Multiplicative NNReal → ℝ)) := by
  exact (linearIndependent_monoidHom (Multiplicative NNReal) ℝ).comp
    (fun i ↦ exponentialCharacter (rate i)) (exponentialCharacter_injective.comp hrate)

noncomputable def gaussianFourier (A : Matrix D D ℝ) (v : D → ℝ) : ℝ :=
  Real.exp (-quadraticValue A v / 2)

/-- No nonsingularity or positive definiteness is required for this algebraic
independence statement; symmetric distinct quadratic forms suffice. -/
theorem gaussianFourier_independent (A : I → Matrix D D ℝ)
    (hs : ∀ k i j, A k i j = A k j i) (hA : Function.Injective A) :
    LinearIndependent ℝ (fun i ↦ gaussianFourier (A i)) := by
  classical
  obtain ⟨v, hv⟩ := exists_covariance_separating_vector A hs hA
  have hr : Function.Injective (fun i ↦ -quadraticValue (A i) v / 2) := by
    intro i j hij
    apply hv
    linarith
  have hl := exponential_characters_independent _ hr
  apply Fintype.linearIndependent_iff.mpr
  intro coefficients heq
  apply Fintype.linearIndependent_iff.mp hl coefficients
  funext t
  have hh := congrFun heq (Real.sqrt ((Multiplicative.toAdd t : NNReal) : ℝ) • v)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    gaussianFourier, quadraticValue_smul,
    Real.sq_sqrt (NNReal.coe_nonneg (Multiplicative.toAdd t))] at hh
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    exponentialCharacter, MonoidHom.coe_mk, OneHom.coe_mk,
    show ∀ a b : ℝ, -(a * b) / 2 = (-b / 2) * a by intros; ring] using hh

def SymmetricCovariance (D : Type*) := {A : Matrix D D ℝ // ∀ i j, A i j = A j i}

theorem all_gaussianFourier_independent :
    LinearIndependent ℝ (fun A : SymmetricCovariance D ↦ gaussianFourier A.val) := by
  classical
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro s
  apply gaussianFourier_independent (fun A : s ↦ A.val.val)
  · exact fun A ↦ A.val.property
  · intro A B h
    exact Subtype.ext (Subtype.ext h)

def permuteCovariance (A : SymmetricCovariance D) (π : Equiv.Perm D) : SymmetricCovariance D :=
  ⟨fun i j ↦ A.val (π i) (π j), fun i j ↦ A.property (π i) (π j)⟩

omit [Fintype D] in
@[simp] theorem permuteCovariance_one (A : SymmetricCovariance D) : permuteCovariance A 1 = A := rfl

omit [Fintype D] in
theorem permuteCovariance_mul (A : SymmetricCovariance D) (π ρ : Equiv.Perm D) :
    permuteCovariance (permuteCovariance A π) ρ = permuteCovariance A (π * ρ) := rfl

noncomputable def orbitFourier (A : SymmetricCovariance D) (v : D → ℝ) : ℝ := by
  classical
  exact ∑ π : Equiv.Perm D, gaussianFourier (permuteCovariance A π).val v

theorem orbitFourier_eq_iff (A B : SymmetricCovariance D) :
    orbitFourier A = orbitFourier B ↔ ∃ π : Equiv.Perm D, permuteCovariance A π = B := by
  classical
  constructor
  · intro h
    have hlin : Finsupp.linearCombination ℝ (fun C : SymmetricCovariance D ↦ gaussianFourier C.val)
        (∑ π : Equiv.Perm D, Finsupp.single (permuteCovariance A π) (1 : ℝ)) =
        Finsupp.linearCombination ℝ (fun C : SymmetricCovariance D ↦ gaussianFourier C.val)
        (∑ π : Equiv.Perm D, Finsupp.single (permuteCovariance B π) (1 : ℝ)) := by
      simp only [map_sum, Finsupp.linearCombination_single, one_smul]
      funext v
      simpa only [Finset.sum_apply, orbitFourier] using congrFun h v
    have hc := congrArg (fun f : SymmetricCovariance D →₀ ℝ ↦ f B)
      (all_gaussianFourier_independent.finsuppLinearCombination_injective hlin)
    by_contra hn
    push_neg at hn
    have ha : (∑ π : Equiv.Perm D, Finsupp.single (permuteCovariance A π) (1 : ℝ)) B = 0 := by
      simp [hn]
    have hb : 0 < (∑ π : Equiv.Perm D, Finsupp.single (permuteCovariance B π) (1 : ℝ)) B := by
      rw [Finsupp.finset_sum_apply]
      apply Finset.sum_pos'
      · intro π _
        simp only [Finsupp.single_apply]
        split_ifs <;> norm_num
      · exact ⟨1, Finset.mem_univ _, by simp⟩
    linarith
  · rintro ⟨π, rfl⟩
    funext v
    unfold orbitFourier
    simp only [permuteCovariance_mul]
    exact (Equiv.sum_comp (Equiv.mulLeft π)
      (fun ρ : Equiv.Perm D ↦ gaussianFourier (permuteCovariance A ρ).val v)).symm

end Descent.Portability.GaussianCovarianceSeparation
