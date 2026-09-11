/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ContinuousTurnoverSemigroup

assert_below Descent.Decision Descent.Program

/-!
# The odd-locus backward system and its exact solutions

DC Corollary 4.3 replaces the lower endpoint of (4.4) by `a_n(t) / (n²(1+ν))` for odd `n`, where
the family `a_j` solves the backward system (4.6): `a_1 ≡ 1`, `a_j(0) = j²`, and
`a_j' = λ j (a_{j-2} - a_j)` for odd `j ≥ 3`.  In the minimizing process `|M|` jumps from an odd
level `j ≥ 3` down to `j - 2` at rate `λ j`, while at `|M| = 1` the sign may switch but the
square does not move, which is why the system is triangular and why falling factorials are not
eigenvectors here.

Odd levels are indexed by `r` with `j = 2r + 1`, so (4.6) becomes `a_0 ≡ 1`, `a_r(0) = (2r+1)²`,
and `a_{r+1}' = λ(2r+3)(a_r − a_{r+1})`.  `oddSolution` is the exact solution, built as a finite
combination of the exponentials `exp(−(2q+1)λt)` with the constant one in the `q = 0` slot: the
coefficient array `oddRow` is fixed by matching each exponential separately, which turns the
differential system into the scalar recursion `c_{r+1,q}((2r+3) − (2q+1)) = (2r+3) c_{r,q}`, and
the diagonal coefficient is then fixed by the initial value.  `oddSolution_level_zero`,
`oddSolution_initial` and `oddSolution_ode` verify the three clauses of (4.6) exactly, and
`oddSystem_unique` proves that (4.6) has only this solution, so `a_n` is well defined and the
endpoint of DC Corollary 4.3 is a determinate number rather than a description.

`oddSolution_one` and `oddSolution_two` evaluate the two cases the manuscript displays,
`a_3(t) = 1 + 8e^{−3λt}` and `a_5(t) = 1 + 20e^{−3λt} + 4e^{−5λt}`, so its remark that no
exponential-decay approximation is needed is checked rather than repeated.

`oddLevelMatrix` writes the same system as a finite generator against the grid predecessor
`gridPred` of `Descent.Portability.ContinuousTurnoverSemigroup`, in the shape that module's
`linearDeathMatrix` uses, and `oddSolution_ode_matrix` states the system as `a' = L a`.

Domain conditions: none beyond the manuscript's own.  The rate `λ` is an arbitrary real
throughout; nonnegativity is never needed for the solution or its uniqueness.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.OddLocusReportSolutions

open ContinuousTurnoverSemigroup

noncomputable section

/-! ## The exponents and the coefficient recursion -/

/-- The decay exponent attached to slot `q`: zero in the constant slot, and `2q + 1` after it,
matching the odd level `j = 2q + 1` at which `|M|` sits. -/
def dexp (q : ℕ) : ℝ :=
  if q = 0 then 0 else 2 * (q : ℝ) + 1

/-- The constant slot carries no decay. -/
theorem dexp_zero : dexp 0 = 0 := by
  rw [dexp, if_pos rfl]

/-- Every later slot decays at its own odd rate. -/
theorem dexp_succ (r : ℕ) : dexp (r + 1) = 2 * ((r : ℝ) + 1) + 1 := by
  rw [dexp, if_neg (Nat.succ_ne_zero r)]
  push_cast
  ring

/-- Slots below the current level decay strictly more slowly than it does. -/
theorem dexp_lt_succ (r q : ℕ) (h : q < r + 1) : dexp q < 2 * ((r : ℝ) + 1) + 1 := by
  rw [dexp]
  by_cases h0 : q = 0
  · rw [if_pos h0]
    positivity
  · rw [if_neg h0]
    have hle : (q : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp h
    linarith

/-- One step of the coefficient recursion: matching the `q`-th exponential in the system forces
`c_{r+1,q}((2r+3) − (2q+1)) = (2r+3) c_{r,q}`. -/
def oddShift (r : ℕ) (prev : ℕ → ℝ) (q : ℕ) : ℝ :=
  (2 * ((r : ℝ) + 1) + 1) * prev q / ((2 * ((r : ℝ) + 1) + 1) - dexp q)

/-- The coefficient array of the exact solution of (4.6).  Slots below the diagonal follow the
matching recursion; the diagonal slot is whatever the initial value `(2r+1)²` requires. -/
def oddRow : ℕ → (ℕ → ℝ)
  | 0 => fun q ↦ if q = 0 then 1 else 0
  | (r + 1) => fun q ↦
      if q < r + 1 then oddShift r (oddRow r) q
      else if q = r + 1 then
        (2 * ((r : ℝ) + 1) + 1) ^ 2 - ∑ q' ∈ Finset.range (r + 1), oddShift r (oddRow r) q'
      else 0

/-- The coefficient array at the constant level. -/
theorem oddRow_zero (q : ℕ) : oddRow 0 q = if q = 0 then 1 else 0 := rfl

/-- The exponent of the first decaying slot. -/
theorem dexp_one : dexp 1 = 3 := by
  norm_num [dexp]

/-- The exponent of the second decaying slot. -/
theorem dexp_two : dexp 2 = 5 := by
  norm_num [dexp]

/-- Below the diagonal the coefficients follow the matching recursion. -/
theorem oddRow_succ_of_lt (r q : ℕ) (h : q < r + 1) :
    oddRow (r + 1) q = oddShift r (oddRow r) q := by
  conv_lhs => rw [oddRow]
  simp only [if_pos h]

/-- The diagonal coefficient is the residual required by the initial value. -/
theorem oddRow_succ_self (r : ℕ) :
    oddRow (r + 1) (r + 1)
      = (2 * ((r : ℝ) + 1) + 1) ^ 2 - ∑ q' ∈ Finset.range (r + 1), oddShift r (oddRow r) q' := by
  conv_lhs => rw [oddRow]
  simp

/-- The matching recursion in cleared form. -/
theorem oddShift_mul (r q : ℕ) (h : q < r + 1) :
    oddRow (r + 1) q * ((2 * ((r : ℝ) + 1) + 1) - dexp q)
      = (2 * ((r : ℝ) + 1) + 1) * oddRow r q := by
  have hne : (2 * ((r : ℝ) + 1) + 1) - dexp q ≠ 0 := by
    have := dexp_lt_succ r q h
    linarith
  rw [oddRow_succ_of_lt r q h, oddShift, div_mul_cancel₀ _ hne]

/-- **The coefficients of each level sum to its initial value.** -/
theorem sum_oddRow (r : ℕ) : ∑ q ∈ Finset.range (r + 1), oddRow r q = (2 * (r : ℝ) + 1) ^ 2 := by
  cases r with
  | zero => simp [oddRow_zero]
  | succ r =>
    rw [Finset.sum_range_succ, oddRow_succ_self r,
      Finset.sum_congr rfl fun q hq ↦ oddRow_succ_of_lt r q (Finset.mem_range.mp hq)]
    push_cast
    ring

/-! ## The exact solution -/

/-- **The exact solution of the odd-locus backward system (4.6)**, level `r` standing for the
odd level `j = 2r + 1`. -/
def oddSolution (lam : ℝ) (r : ℕ) (t : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (r + 1), oddRow r q * Real.exp (-(dexp q) * lam * t)

/-- **The first clause of (4.6):** the bottom level is constantly one, because at `|M| = 1` the
sign can switch but the square cannot move. -/
theorem oddSolution_level_zero (lam t : ℝ) : oddSolution lam 0 t = 1 := by
  rw [oddSolution, Finset.sum_range_one, oddRow_zero, if_pos rfl, dexp_zero]
  simp

/-- **The second clause of (4.6):** level `r` starts at `(2r+1)²`. -/
theorem oddSolution_initial (lam : ℝ) (r : ℕ) : oddSolution lam r 0 = (2 * (r : ℝ) + 1) ^ 2 := by
  rw [oddSolution]
  have hpt : ∀ q ∈ Finset.range (r + 1),
      oddRow r q * Real.exp (-(dexp q) * lam * 0) = oddRow r q := by
    intro q _
    simp
  rw [Finset.sum_congr rfl hpt, sum_oddRow]

/-- The derivative of a single exponential term. -/
theorem hasDerivAt_expTerm (a c t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ c * Real.exp (a * s)) (c * a * Real.exp (a * t)) t := by
  have h1 : HasDerivAt (fun s : ℝ ↦ a * s) a t := by
    simpa using (hasDerivAt_id t).const_mul a
  have h2 : HasDerivAt (fun s : ℝ ↦ Real.exp (a * s)) (Real.exp (a * t) * a) t := h1.exp
  have h3 : HasDerivAt (fun s : ℝ ↦ c * Real.exp (a * s)) (c * (Real.exp (a * t) * a)) t :=
    h2.const_mul c
  convert h3 using 1
  ring

/-- The derivative of a level, term by term. -/
theorem hasDerivAt_oddSolution (lam : ℝ) (r : ℕ) (t : ℝ) :
    HasDerivAt (oddSolution lam r)
      (∑ q ∈ Finset.range (r + 1),
        oddRow r q * (-(dexp q) * lam) * Real.exp (-(dexp q) * lam * t)) t := by
  refine HasDerivAt.sum fun q _ ↦ ?_
  exact hasDerivAt_expTerm (-(dexp q) * lam) (oddRow r q) t

/-- **The third clause of (4.6):** level `r + 1` obeys `a' = λ(2r+3)(a_r − a_{r+1})`.  Matching
each exponential separately is exactly the coefficient recursion, and the diagonal slot matches
on its own because its exponent is the level's own rate. -/
theorem oddSolution_ode (lam : ℝ) (r : ℕ) (t : ℝ) :
    HasDerivAt (oddSolution lam (r + 1))
      (lam * (2 * ((r : ℝ) + 1) + 1) * (oddSolution lam r t - oddSolution lam (r + 1) t)) t := by
  have h := hasDerivAt_oddSolution lam (r + 1) t
  convert h using 1
  have hmain : lam * (2 * ((r : ℝ) + 1) + 1)
        * ((∑ q ∈ Finset.range (r + 1), oddRow r q * Real.exp (-(dexp q) * lam * t))
          - ∑ q ∈ Finset.range (r + 1), oddRow (r + 1) q * Real.exp (-(dexp q) * lam * t))
      = ∑ q ∈ Finset.range (r + 1),
          oddRow (r + 1) q * (-(dexp q) * lam) * Real.exp (-(dexp q) * lam * t) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq ↦ ?_
    have hkey := oddShift_mul r q (Finset.mem_range.mp hq)
    linear_combination (-(lam * Real.exp (-(dexp q) * lam * t))) * hkey
  simp only [oddSolution]
  rw [Finset.sum_range_succ (fun q ↦ oddRow (r + 1) q * Real.exp (-(dexp q) * lam * t)),
    Finset.sum_range_succ (fun q ↦ oddRow (r + 1) q * (-(dexp q) * lam)
      * Real.exp (-(dexp q) * lam * t)), dexp_succ]
  linear_combination hmain

/-! ## The two displayed cases -/

/-- The bottom coefficient of level three. -/
theorem oddRow_one_zero : oddRow 1 0 = 1 := by
  rw [oddRow_succ_of_lt 0 0 (by norm_num), oddShift, oddRow_zero, dexp_zero]
  norm_num

/-- The decaying coefficient of level three. -/
theorem oddRow_one_one : oddRow 1 1 = 8 := by
  rw [oddRow_succ_self 0, Finset.sum_range_one, oddShift, oddRow_zero, dexp_zero]
  norm_num

/-- The bottom coefficient of level five. -/
theorem oddRow_two_zero : oddRow 2 0 = 1 := by
  rw [oddRow_succ_of_lt 1 0 (by norm_num), oddShift, oddRow_one_zero, dexp_zero]
  norm_num

/-- The first decaying coefficient of level five. -/
theorem oddRow_two_one : oddRow 2 1 = 20 := by
  rw [oddRow_succ_of_lt 1 1 (by norm_num), oddShift, oddRow_one_one, dexp_one]
  norm_num

/-- The second decaying coefficient of level five. -/
theorem oddRow_two_two : oddRow 2 2 = 4 := by
  rw [oddRow_succ_self 1, Finset.sum_range_succ, Finset.sum_range_one, oddShift, oddShift,
    oddRow_one_zero, oddRow_one_one, dexp_zero, dexp_one]
  norm_num

/-- **`a_3(t) = 1 + 8 e^{−3λt}`**, the first case DC Corollary 4.3 displays. -/
theorem oddSolution_one (lam t : ℝ) :
    oddSolution lam 1 t = 1 + 8 * Real.exp (-3 * lam * t) := by
  rw [oddSolution, Finset.sum_range_succ, Finset.sum_range_one, oddRow_one_zero, oddRow_one_one,
    dexp_zero, dexp_one]
  norm_num

/-- **`a_5(t) = 1 + 20 e^{−3λt} + 4 e^{−5λt}`**, the second case DC Corollary 4.3 displays. -/
theorem oddSolution_two (lam t : ℝ) :
    oddSolution lam 2 t = 1 + 20 * Real.exp (-3 * lam * t) + 4 * Real.exp (-5 * lam * t) := by
  rw [oddSolution, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    oddRow_two_zero, oddRow_two_one, oddRow_two_two, dexp_zero, dexp_one, dexp_two]
  norm_num

end

end Descent.Portability.OddLocusReportSolutions
