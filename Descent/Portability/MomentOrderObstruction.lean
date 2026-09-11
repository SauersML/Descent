/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RadialInterpolation
import Mathlib.Algebra.Group.ForwardDiff

assert_below Descent.Decision Descent.Program

/-!
# No fixed joint-moment order identifies an expected fitted report

DC Lemmas 8.1 and 8.2. For every `k` the alternating binomial weights of order `k+1`,
split by sign, give two finitely supported laws on the arithmetic progression
`a, a+h, …, a+(k+1)h` with identical moments through degree `k`, and their expectations
of a test function differ by exactly `2^{-k}` times its `(k+1)`-st finite difference.
The hypotheses are the manuscript's domain conditions: a polynomial of degree at most
`k` for the matching statement, a nonzero finite difference for the separation.

The annihilation step is Mathlib's `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`. The
step from "real analytic and not a polynomial" to "some finite difference is nonzero"
is a Taylor estimate that is NOT formalized here; instead each concrete report below
comes with an explicit nonzero finite difference, and the "for every finite `k`" form of
DC Theorems 8.3 and 8.4 is proved unconditionally through
`RadialInterpolation.radial_report_gap`, which needs no analyticity at all. The laws are
`Portability.weightedExp` probability vectors on `Fin (k+2)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MomentOrderObstruction

open Foundations fwdDiff

noncomputable section

/-- The signed binomial weight of DC equation (8.1). -/
def alternatingWeight (k j : ℕ) : ℝ := (-1) ^ j * ((k + 1).choose j : ℝ) / 2 ^ k

/-- The magnitude of the signed binomial weight is the normalized binomial
coefficient. -/
theorem abs_alternatingWeight (k j : ℕ) :
    |alternatingWeight k j| = ((k + 1).choose j : ℝ) / 2 ^ k := by
  have h1 : |(-1 : ℝ) ^ j| = 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
  have h2 : |((k + 1).choose j : ℝ)| = ((k + 1).choose j : ℝ) :=
    abs_of_nonneg (by positivity)
  have h3 : |(2 : ℝ) ^ k| = 2 ^ k := abs_of_nonneg (by positivity)
  unfold alternatingWeight
  rw [abs_div, abs_mul, h1, h2, h3, one_mul]

/-- **The annihilation identity.** The alternating binomial weights of order `k+1` kill
every polynomial of degree at most `k` sampled on an arithmetic progression. -/
theorem alternating_annihilates (k : ℕ) (a step : ℝ) (P : Polynomial ℝ)
    (hdeg : P.natDegree ≤ k) :
    ∑ j ∈ Finset.range (k + 2),
      (-1 : ℝ) ^ j * ((k + 1).choose j : ℝ) * P.eval (a + j * step) = 0 := by
  set Q : Polynomial ℝ := P.comp (Polynomial.C step * Polynomial.X + Polynomial.C a)
    with hQdef
  have hlin : (Polynomial.C step * Polynomial.X + Polynomial.C a).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact Polynomial.natDegree_mul_le.trans (by simp)
    · simp
  have hQdeg : Q.natDegree < k + 1 := by
    refine lt_of_le_of_lt (Polynomial.natDegree_comp_le.trans ?_) (Nat.lt_succ_self k)
    calc P.natDegree * (Polynomial.C step * Polynomial.X + Polynomial.C a).natDegree
        ≤ P.natDegree * 1 := Nat.mul_le_mul_left _ hlin
      _ = P.natDegree := by ring
      _ ≤ k := hdeg
  have hzero : Δ_[(1 : ℝ)]^[k + 1] Q.eval = 0 :=
    Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hQdeg
  have hexp := fwdDiff_iter_eq_sum_shift (1 : ℝ) Q.eval (k + 1) 0
  rw [hzero] at hexp
  have hval : ∀ j : ℕ, Q.eval ((0 : ℝ) + (j : ℕ) • (1 : ℝ)) = P.eval (a + j * step) := by
    intro j
    simp only [hQdef, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, nsmul_eq_mul, mul_one, zero_add]
    ring_nf
  have hsum : ∑ j ∈ Finset.range (k + 2),
      ((-1 : ℝ) ^ (k + 1 - j) * ((k + 1).choose j : ℝ)) * P.eval (a + j * step) = 0 := by
    have := hexp.symm
    simp only [Pi.zero_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← hval j, zsmul_eq_mul]
    push_cast
    ring
  have hsign : ∀ j ∈ Finset.range (k + 2),
      ((-1 : ℝ) ^ (k + 1 - j) * ((k + 1).choose j : ℝ)) * P.eval (a + j * step) =
        (-1 : ℝ) ^ (k + 1) *
          ((-1 : ℝ) ^ j * ((k + 1).choose j : ℝ) * P.eval (a + j * step)) := by
    intro j hj
    have hjle : j ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hsq : ((-1 : ℝ) ^ j) * ((-1 : ℝ) ^ j) = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨j, rfl⟩
    have hcancel : (-1 : ℝ) ^ (k + 1 - j) * (-1 : ℝ) ^ j = (-1 : ℝ) ^ (k + 1) := by
      rw [← pow_add, Nat.sub_add_cancel hjle]
    have hkey : (-1 : ℝ) ^ (k + 1 - j) = (-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ j := by
      calc (-1 : ℝ) ^ (k + 1 - j)
          = (-1 : ℝ) ^ (k + 1 - j) * ((-1 : ℝ) ^ j * (-1 : ℝ) ^ j) := by rw [hsq, mul_one]
        _ = ((-1 : ℝ) ^ (k + 1 - j) * (-1 : ℝ) ^ j) * (-1 : ℝ) ^ j := by ring
        _ = (-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ j := by rw [hcancel]
    rw [hkey]; ring
  rw [Finset.sum_congr rfl hsign, ← Finset.mul_sum] at hsum
  have hne : ((-1 : ℝ) ^ (k + 1)) ≠ 0 := by
    intro hc
    have := abs_eq_zero.mpr hc
    rw [abs_pow, abs_neg, abs_one, one_pow] at this
    norm_num at this
  exact (mul_eq_zero.mp hsum).resolve_left hne

/-- The signed binomial weights sum to zero, so the two parity laws are both
normalized. -/
theorem sum_alternatingWeight (k : ℕ) :
    ∑ j ∈ Finset.range (k + 2), alternatingWeight k j = 0 := by
  have h := alternating_annihilates k 0 0 1 (by simp)
  simp only [Polynomial.eval_one, mul_one] at h
  unfold alternatingWeight
  rw [← Finset.sum_div, h, zero_div]

/-- The signed binomial weights have total variation two. -/
theorem sum_abs_alternatingWeight (k : ℕ) :
    ∑ j ∈ Finset.range (k + 2), |alternatingWeight k j| = 2 := by
  have h2k : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  have hnat : ∑ j ∈ Finset.range (k + 2), ((k + 1).choose j : ℝ) = 2 ^ (k + 1) := by
    exact_mod_cast Nat.sum_range_choose (k + 1)
  simp only [abs_alternatingWeight]
  rw [← Finset.sum_div, hnat, pow_succ]
  field_simp

/-- The parity laws `P₊` (`s = false`) and `P₋` (`s = true`) of DC equation (8.1). -/
def parityMass (k : ℕ) (s : Bool) (j : ℕ) : ℝ :=
  if s then (|alternatingWeight k j| - alternatingWeight k j) / 2
  else (|alternatingWeight k j| + alternatingWeight k j) / 2

/-- Each parity mass is nonnegative. -/
theorem parityMass_nonneg (k : ℕ) (s : Bool) (j : ℕ) : 0 ≤ parityMass k s j := by
  unfold parityMass
  split
  · linarith [le_abs_self (alternatingWeight k j)]
  · linarith [neg_abs_le (alternatingWeight k j)]

/-- Each parity law is a probability law. -/
theorem parityMass_sum (k : ℕ) (s : Bool) :
    ∑ j : Fin (k + 2), parityMass k s j = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ parityMass k s j) (k + 2)]
  have hsplit : ∀ j : ℕ, parityMass k s j =
      (|alternatingWeight k j| + (if s then -1 else 1) * alternatingWeight k j) / 2 := by
    intro j
    unfold parityMass
    split <;> ring
  rw [Finset.sum_congr rfl fun j _ ↦ hsplit j, ← Finset.sum_div, Finset.sum_add_distrib,
    ← Finset.mul_sum, sum_alternatingWeight, sum_abs_alternatingWeight]
  ring

/-- The two moment-matched expectations of DC Lemma 8.1. -/
def parityExp (k : ℕ) (s : Bool) : ExpFunctional (Fin (k + 2)) :=
  weightedExp (fun j ↦ parityMass k s j) (fun j ↦ parityMass_nonneg k s j)
    (parityMass_sum k s)

/-- **DC Lemma 8.1, gap formula.** The two parity laws differ on any test function by
exactly `2^{-k}` times its `(k+1)`-st finite difference along the progression. -/
theorem parity_gap (k : ℕ) (a step : ℝ) (f : ℝ → ℝ) :
    parityExp k false (fun j ↦ f (a + (j : ℕ) * step)) -
        parityExp k true (fun j ↦ f (a + (j : ℕ) * step)) =
      (∑ j ∈ Finset.range (k + 2),
        (-1 : ℝ) ^ j * ((k + 1).choose j : ℝ) * f (a + j * step)) / 2 ^ k := by
  simp only [parityExp, weightedExp_apply]
  rw [← Finset.sum_sub_distrib,
    Fin.sum_univ_eq_sum_range
      (fun j ↦ parityMass k false j * f (a + j * step) -
        parityMass k true j * f (a + j * step)) (k + 2),
    Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hdiff : parityMass k false j - parityMass k true j = alternatingWeight k j := by
    have h0 : parityMass k false j =
        (|alternatingWeight k j| + alternatingWeight k j) / 2 := rfl
    have h1 : parityMass k true j =
        (|alternatingWeight k j| - alternatingWeight k j) / 2 := rfl
    rw [h0, h1]; ring
  have hfac : parityMass k false j * f (a + j * step) -
      parityMass k true j * f (a + j * step) =
        (parityMass k false j - parityMass k true j) * f (a + j * step) := by ring
  rw [hfac, hdiff]
  unfold alternatingWeight
  ring

/-- **DC Lemma 8.1, moment matching.** The two parity laws share every moment through
degree `k`. -/
theorem parity_moment_match (k : ℕ) (a step : ℝ) (P : Polynomial ℝ)
    (hdeg : P.natDegree ≤ k) :
    parityExp k false (fun j ↦ P.eval (a + (j : ℕ) * step)) =
      parityExp k true (fun j ↦ P.eval (a + (j : ℕ) * step)) := by
  have h := parity_gap k a step (fun x ↦ P.eval x)
  rw [alternating_annihilates k a step P hdeg, zero_div] at h
  linarith

/-- **DC Lemma 8.2, usable form.** A nonzero `(k+1)`-st finite difference separates the
two moment-matched laws. The manuscript deduces such a finite difference from real
analyticity and nonpolynomiality by a Taylor estimate; that deduction is not formalized
here, and every application below supplies the finite difference explicitly. -/
theorem parity_separates (k : ℕ) (a step : ℝ) (f : ℝ → ℝ)
    (hne : ∑ j ∈ Finset.range (k + 2),
      (-1 : ℝ) ^ j * ((k + 1).choose j : ℝ) * f (a + j * step) ≠ 0) :
    parityExp k false (fun j ↦ f (a + (j : ℕ) * step)) ≠
      parityExp k true (fun j ↦ f (a + (j : ℕ) * step)) := by
  intro hEq
  have h := parity_gap k a step f
  rw [hEq, sub_self] at h
  have h2k : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  exact hne (by field_simp at h; linarith [h])

end

end Descent.Portability.MomentOrderObstruction
