/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ApproximationDuality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev

assert_below Descent.Decision Descent.Program

/-!
# Denominator-aware finite-moment recovery

PL Theorem 9.1, the positive closure. When the report is a ratio `A/B` with
`0 ≤ A ≤ B` and the denominator confined to a window `0 < δ ≤ B ≤ M`, the Chebyshev
construction (9.2) gives an explicit polynomial `p` of degree at most `j-1` such that
`A · p(B)` approximates `A/B` uniformly within `ε_j = 1/T_j(c)`, where `c = (M+δ)/(M-δ)`,
and `ε_j = 2ρ^j/(1+ρ^{2j})` with `ρ = (√κ-1)/(√κ+1)` and `κ = M/δ`. Moments through
degree `d·j` therefore determine the expectation of the approximant, and two laws
agreeing on it report expectations at most `2ε_j` apart. The hypotheses are exactly the
manuscript's domain conditions (9.1).

This is the counterpart to `ApproximationDuality.information_diameter_duality` and
`RadialInterpolation.radial_report_gap`, which show that without a denominator bound no
finite moment order helps at all. Laws are `Portability.weightedExp` probability vectors.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.DenominatorAwareRecovery

open Foundations

noncomputable section

/-- The Chebyshev evaluation point `c = (M+δ)/(M-δ)` of PL Theorem 9.1. -/
def chebC (M δ : ℝ) : ℝ := (M + δ) / (M - δ)

/-- The geometric ratio `ρ = (√κ - 1)/(√κ + 1)` with `κ = M/δ`. -/
def chebRho (M δ : ℝ) : ℝ := (Real.sqrt (M / δ) - 1) / (Real.sqrt (M / δ) + 1)

/-- The affine map carrying the denominator window `[δ, M]` onto `[-1, 1]`. -/
def chebArgPoly (M δ : ℝ) : Polynomial ℝ :=
  Polynomial.C ((M + δ) / (M - δ)) - Polynomial.C (2 / (M - δ)) * Polynomial.X

/-- The Chebyshev peak `T_j(c)`, whose reciprocal is the error level `ε_j`. -/
def chebPeak (M δ : ℝ) (j : ℕ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (chebC M δ)

/-- The residual polynomial `r_j` of PL equation (9.2). -/
def residualPoly (M δ : ℝ) (j : ℕ) : Polynomial ℝ :=
  Polynomial.C (chebPeak M δ j)⁻¹ *
    (Polynomial.Chebyshev.T ℝ (j : ℤ)).comp (chebArgPoly M δ)

/-- The recovery polynomial `p_{j-1}` of PL equation (9.2). -/
def recoveryPoly (M δ : ℝ) (j : ℕ) : Polynomial ℝ :=
  (1 - residualPoly M δ j) /ₘ Polynomial.X

/-- Chebyshev polynomials at `(z + z⁻¹)/2` evaluate to `(zⁿ + z⁻ⁿ)/2`. -/
theorem chebyshev_eval_half_add_inv (z : ℝ) (hz : 0 < z) (n : ℕ) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval ((z + z⁻¹) / 2) =
      (z ^ n + (z⁻¹) ^ n) / 2 := by
  have hcosh : Real.cosh (Real.log z) = (z + z⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_log hz, Real.exp_neg, Real.exp_log hz]
  have hpow : Real.exp ((n : ℝ) * Real.log z) = z ^ n := by
    rw [mul_comm, ← Real.rpow_def_of_pos hz, Real.rpow_natCast]
  have hcast : ((n : ℤ) : ℝ) * Real.log z = (n : ℝ) * Real.log z := by push_cast; ring
  rw [← hcosh, Polynomial.Chebyshev.T_real_cosh, Real.cosh_eq, hcast, hpow,
    Real.exp_neg, hpow, ← inv_pow]

/-- The Chebyshev degree grows at most linearly. -/
theorem natDegree_T_le (n : ℕ) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).natDegree ≤ n := by
  have key : ∀ m : ℕ, (Polynomial.Chebyshev.T ℝ (m : ℤ)).natDegree ≤ m ∧
      (Polynomial.Chebyshev.T ℝ ((m + 1 : ℕ) : ℤ)).natDegree ≤ m + 1 := by
    intro m
    induction m with
    | zero => constructor <;> simp
    | succ p ih =>
      refine ⟨ih.2, ?_⟩
      have h1 : (Polynomial.Chebyshev.T ℝ ((p : ℤ) + 1)).natDegree ≤ p + 1 := by
        have h := ih.2
        rwa [show ((p + 1 : ℕ) : ℤ) = (p : ℤ) + 1 by push_cast; ring] at h
      have hc : ((p + 1 + 1 : ℕ) : ℤ) = (p : ℤ) + 2 := by push_cast; ring
      rw [hc, Polynomial.Chebyshev.T_add_two]
      refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · refine Polynomial.natDegree_mul_le.trans ?_
        have h2 : ((2 : Polynomial ℝ) * Polynomial.X).natDegree ≤ 1 :=
          Polynomial.natDegree_mul_le.trans (by simp)
        exact (Nat.add_le_add h2 h1).trans (by omega)
      · exact ih.1.trans (by omega)
  exact (key n).1

/-- On `[-1,1]` every Chebyshev polynomial is bounded by one. -/
theorem abs_T_eval_le_one (y : ℝ) (hy : -1 ≤ y) (hy' : y ≤ 1) (n : ℤ) :
    |(Polynomial.Chebyshev.T ℝ n).eval y| ≤ 1 := by
  rw [← Real.cos_arccos hy hy', Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

section Window

variable (M δ : ℝ)

/-- The geometric ratio is positive under the denominator window. -/
theorem chebRho_pos (hδ : 0 < δ) (hM : δ < M) : 0 < chebRho M δ := by
  have hκ : 1 < M / δ := (one_lt_div hδ).mpr hM
  have hs : 1 < Real.sqrt (M / δ) := by
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ M / δ), Real.sqrt_nonneg (M / δ)]
  exact div_pos (by linarith) (by linarith)

/-- **PL Theorem 9.1, the `ρ` parametrization.** The Chebyshev point is the half sum of
the geometric ratio and its reciprocal. -/
theorem chebC_eq_half_add_inv (hδ : 0 < δ) (hM : δ < M) :
    chebC M δ = (chebRho M δ + (chebRho M δ)⁻¹) / 2 := by
  have hκ : 1 < M / δ := (one_lt_div hδ).mpr hM
  set s := Real.sqrt (M / δ) with hsdef
  have hs2 : s ^ 2 = M / δ := Real.sq_sqrt (by positivity)
  have hs : 1 < s := by nlinarith [Real.sqrt_nonneg (M / δ)]
  have hsm : s - 1 ≠ 0 := by linarith
  have hsp : s + 1 ≠ 0 := by linarith
  have hd : s ^ 2 - 1 ≠ 0 := by nlinarith
  have hMδ : M - δ ≠ 0 := by linarith
  have hM2 : δ * s ^ 2 = M := by rw [hs2]; field_simp
  have hA : ((s - 1) / (s + 1) + ((s - 1) / (s + 1))⁻¹) / 2 = (s ^ 2 + 1) / (s ^ 2 - 1) := by
    rw [inv_div]
    field_simp
    ring
  have hB : (s ^ 2 + 1) / (s ^ 2 - 1) = (M + δ) / (M - δ) := by
    rw [div_eq_div_iff hd hMδ]
    linear_combination (-2 : ℝ) * hM2
  unfold chebC chebRho
  rw [← hsdef, hA, hB]

/-- **PL Theorem 9.1.** The Chebyshev peak in closed geometric form. -/
theorem chebPeak_eq (hδ : 0 < δ) (hM : δ < M) (j : ℕ) :
    chebPeak M δ j = (chebRho M δ ^ j + (chebRho M δ)⁻¹ ^ j) / 2 := by
  unfold chebPeak
  rw [chebC_eq_half_add_inv M δ hδ hM]
  exact chebyshev_eval_half_add_inv _ (chebRho_pos M δ hδ hM) j

/-- The Chebyshev peak is at least one, so the error level is at most one. -/
theorem one_le_chebPeak (hδ : 0 < δ) (hM : δ < M) (j : ℕ) : 1 ≤ chebPeak M δ j := by
  have hρ := chebRho_pos M δ hδ hM
  have hpow : 0 < chebRho M δ ^ j := pow_pos hρ j
  rw [chebPeak_eq M δ hδ hM j, inv_pow]
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), ← sub_nonneg]
  have hid : chebRho M δ ^ j + (chebRho M δ ^ j)⁻¹ - 1 * 2 =
      (chebRho M δ ^ j - 1) ^ 2 / chebRho M δ ^ j := by
    field_simp
    ring
  rw [hid]
  positivity

/-- **PL Theorem 9.1, equation (9.3).** The error level in its geometric form
`2ρ^j/(1+ρ^{2j})`. -/
theorem chebPeak_inv_eq (hδ : 0 < δ) (hM : δ < M) (j : ℕ) :
    1 / chebPeak M δ j = 2 * chebRho M δ ^ j / (1 + chebRho M δ ^ (2 * j)) := by
  have hρ := chebRho_pos M δ hδ hM
  have hpow : 0 < chebRho M δ ^ j := pow_pos hρ j
  have h2 : chebRho M δ ^ (2 * j) = (chebRho M δ ^ j) ^ 2 := by
    rw [← pow_mul, mul_comm]
  rw [chebPeak_eq M δ hδ hM j, inv_pow, h2]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  field_simp
  ring

/-- The affine window map evaluates to `(M + δ - 2b)/(M - δ)`. -/
theorem chebArgPoly_eval (b : ℝ) :
    (chebArgPoly M δ).eval b = (M + δ - 2 * b) / (M - δ) := by
  unfold chebArgPoly
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- The affine window map carries `[δ, M]` into `[-1, 1]`. -/
theorem chebArgPoly_mem (hM : δ < M) (b : ℝ) (hbl : δ ≤ b) (hbu : b ≤ M) :
    -1 ≤ (chebArgPoly M δ).eval b ∧ (chebArgPoly M δ).eval b ≤ 1 := by
  have hpos : 0 < M - δ := by linarith
  rw [chebArgPoly_eval]
  constructor
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_le_one hpos]; linarith

/-- The affine window map has degree at most one. -/
theorem natDegree_chebArgPoly_le : (chebArgPoly M δ).natDegree ≤ 1 := by
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) ?_)
  exact Polynomial.natDegree_mul_le.trans (by simp)

/-- The residual polynomial has degree at most `j`. -/
theorem natDegree_residualPoly_le (j : ℕ) : (residualPoly M δ j).natDegree ≤ j := by
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine Polynomial.natDegree_comp_le.trans ?_
  exact (Nat.mul_le_mul (natDegree_T_le j) (natDegree_chebArgPoly_le M δ)).trans (by omega)

/-- The residual polynomial is one at the origin, which is what makes the recovery rule
a polynomial. -/
theorem residualPoly_eval_zero (hδ : 0 < δ) (hM : δ < M) (j : ℕ) :
    (residualPoly M δ j).eval 0 = 1 := by
  have hpeak : chebPeak M δ j ≠ 0 := by
    have := one_le_chebPeak M δ hδ hM j
    linarith
  unfold residualPoly
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, chebArgPoly_eval]
  have harg : (M + δ - 2 * 0) / (M - δ) = chebC M δ := by
    unfold chebC
    norm_num
  rw [harg]
  exact inv_mul_cancel₀ hpeak

/-- **PL equation (9.2).** `1 - r_j` factors through the origin, and the quotient is the
recovery polynomial. -/
theorem recoveryPoly_factor (hδ : 0 < δ) (hM : δ < M) (j : ℕ) :
    1 - residualPoly M δ j = Polynomial.X * recoveryPoly M δ j := by
  have hdvd : Polynomial.X ∣ (1 - residualPoly M δ j) := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    simp [residualPoly_eval_zero M δ hδ hM j]
  have hmonic : (Polynomial.X : Polynomial ℝ).Monic := Polynomial.monic_X
  have hmod : (1 - residualPoly M δ j) %ₘ (Polynomial.X : Polynomial ℝ) = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mpr hdvd
  have h := Polynomial.modByMonic_add_div (1 - residualPoly M δ j) hmonic
  rw [hmod, zero_add] at h
  exact h.symm

/-- **PL Theorem 9.1, degree bound.** The recovery polynomial has degree at most
`j - 1`. -/
theorem natDegree_recoveryPoly_le (j : ℕ) : (recoveryPoly M δ j).natDegree ≤ j - 1 := by
  unfold recoveryPoly
  rw [Polynomial.natDegree_divByMonic _ Polynomial.monic_X, Polynomial.natDegree_X]
  have h : (1 - residualPoly M δ j).natDegree ≤ j :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_residualPoly_le M δ j))
  omega

/-- **PL Theorem 9.1, equation (9.3).** Under the denominator window the explicit
polynomial recovery rule errs by at most `ε_j = 1/T_j(c)`, uniformly over the support. -/
theorem recovery_error_bound (hδ : 0 < δ) (hM : δ < M) (j : ℕ) (A B : ℝ)
    (hA : 0 ≤ A) (hAB : A ≤ B) (hBl : δ ≤ B) (hBu : B ≤ M) :
    |A / B - A * (recoveryPoly M δ j).eval B| ≤ 1 / chebPeak M δ j := by
  have hB : 0 < B := lt_of_lt_of_le hδ hBl
  have hpeak : 1 ≤ chebPeak M δ j := one_le_chebPeak M δ hδ hM j
  have hpeak0 : 0 < chebPeak M δ j := by linarith
  have hfac := congrArg (Polynomial.eval B) (recoveryPoly_factor M δ hδ hM j)
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_X] at hfac
  have hrec : (recoveryPoly M δ j).eval B = (1 - (residualPoly M δ j).eval B) / B := by
    rw [eq_div_iff hB.ne']
    linarith
  rw [hrec, show A / B - A * ((1 - (residualPoly M δ j).eval B) / B) =
      A / B * (residualPoly M δ j).eval B by field_simp; ring, abs_mul]
  have h1 : |A / B| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg hA hB.le)]
    exact (div_le_one hB).mpr hAB
  have h2 : |(residualPoly M δ j).eval B| ≤ 1 / chebPeak M δ j := by
    unfold residualPoly
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (chebPeak M δ j)⁻¹)]
    obtain ⟨hlo, hhi⟩ := chebArgPoly_mem M δ hM B hBl hBu
    have hT := abs_T_eval_le_one ((chebArgPoly M δ).eval B) hlo hhi (j : ℤ)
    calc (chebPeak M δ j)⁻¹ *
          |(Polynomial.Chebyshev.T ℝ (j : ℤ)).eval ((chebArgPoly M δ).eval B)|
        ≤ (chebPeak M δ j)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hT (by positivity)
      _ = 1 / chebPeak M δ j := by rw [mul_one, inv_eq_one_div]
  calc |A / B| * |(residualPoly M δ j).eval B| ≤ 1 * (1 / chebPeak M δ j) :=
        mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = 1 / chebPeak M δ j := one_mul _

/-- **PL Theorem 9.1, moment order.** If numerator and denominator have degree at most
`d`, the approximant has degree at most `d · j`, so raw moments through that degree
determine its expectation. -/
theorem natDegree_approximant_le (j : ℕ) (hj : 1 ≤ j) (d : ℕ) (A B : Polynomial ℝ)
    (hAd : A.natDegree ≤ d) (hBd : B.natDegree ≤ d) :
    (A * (recoveryPoly M δ j).comp B).natDegree ≤ d * j := by
  refine Polynomial.natDegree_mul_le.trans ?_
  have hcomp : ((recoveryPoly M δ j).comp B).natDegree ≤ (j - 1) * d :=
    Polynomial.natDegree_comp_le.trans
      (Nat.mul_le_mul (natDegree_recoveryPoly_le M δ j) hBd)
  have hsum := Nat.add_le_add hAd hcomp
  have harith : d + (j - 1) * d = d * j := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
    simp only [Nat.add_sub_cancel_left]
    ring
  calc A.natDegree + ((recoveryPoly M δ j).comp B).natDegree ≤ d + (j - 1) * d := hsum
    _ = d * j := harith

end Window

/-- A probability average of a uniformly bounded function is bounded by the same
constant. -/
theorem abs_average_le_of_bound {S : Type*} [Fintype S] (p f : S → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hps : ∑ s, p s = 1) (ε : ℝ) (hb : ∀ s, |f s| ≤ ε) :
    |∑ s, p s * f s| ≤ ε := by
  calc |∑ s, p s * f s| ≤ ∑ s, |p s * f s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, p s * ε := by
        refine Finset.sum_le_sum fun s _ ↦ ?_
        rw [abs_mul, abs_of_nonneg (hp s)]
        exact mul_le_mul_of_nonneg_left (hb s) (hp s)
    _ = ε := by rw [← Finset.sum_mul, hps, one_mul]

/-- **PL Theorem 9.1, report bound.** Two finitely supported laws that agree on the
expectation of the degree-`d·j` approximant report expected ratios at most `2ε_j`
apart. -/
theorem matched_report_gap_le {S : Type*} [Fintype S] (M δ : ℝ) (hδ : 0 < δ)
    (hM : δ < M) (j : ℕ) (A B : S → ℝ) (hA : ∀ s, 0 ≤ A s) (hAB : ∀ s, A s ≤ B s)
    (hBl : ∀ s, δ ≤ B s) (hBu : ∀ s, B s ≤ M) (p q : S → ℝ) (hp : ∀ s, 0 ≤ p s)
    (hq : ∀ s, 0 ≤ q s) (hps : ∑ s, p s = 1) (hqs : ∑ s, q s = 1)
    (hmatch : ∑ s, p s * (A s * (recoveryPoly M δ j).eval (B s)) =
      ∑ s, q s * (A s * (recoveryPoly M δ j).eval (B s))) :
    |(∑ s, p s * (A s / B s)) - ∑ s, q s * (A s / B s)| ≤ 2 * (1 / chebPeak M δ j) := by
  have hbound : ∀ s, |A s / B s - A s * (recoveryPoly M δ j).eval (B s)| ≤
      1 / chebPeak M δ j := fun s ↦
    recovery_error_bound M δ hδ hM j (A s) (B s) (hA s) (hAB s) (hBl s) (hBu s)
  have hsplit : ∀ w : S → ℝ, ∑ s, w s = 1 →
      ∑ s, w s * (A s / B s - A s * (recoveryPoly M δ j).eval (B s)) =
        (∑ s, w s * (A s / B s)) -
          ∑ s, w s * (A s * (recoveryPoly M δ j).eval (B s)) := by
    intro w _
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ ↦ by ring
  have h1 := abs_average_le_of_bound p _ hp hps _ hbound
  have h2 := abs_average_le_of_bound q _ hq hqs _ hbound
  rw [hsplit p hps] at h1
  rw [hsplit q hqs] at h2
  have e1 := abs_le.mp h1
  have e2 := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, hmatch]

end

end Descent.Portability.DenominatorAwareRecovery
