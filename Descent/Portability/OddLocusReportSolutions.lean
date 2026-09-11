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
`linearDeathMatrix` uses.  Each coefficient column is an eigenvector of it
(`oddLevelMatrix_eigen`), which is the matching recursion read as an eigenvector equation, so
`exp_oddLevelMatrix_square_report` evaluates the semigroup of that generator on the initial
square report `(2r+1)²` as exactly `a_{2r+1}(t)`.  That last step runs through
`exp_mulVec_eigen`, hence through the Euler limit, not through a differential equation.

`nearestDriftGen_lump` closes the loop back to the coupling: at symmetric rates the count drift
is `b(k) = λ(n − 2k)`, so the nearest-drift chain always steps toward the balance point, and the
aggregate `|2k − n|` therefore falls by exactly two at rate `λ|2k − n|`, which is the odd-level
generator.  At `|2k − n| = 1` the count still moves while the aggregate does not, the
manuscript's remark that the sign can switch while the square stays one.
`driftStep_iterate_lump` carries that to every skeleton horizon, so running the nearest-drift
count chain on a report of the aggregate is running the odd-level chain on that report.

What is not proved here is the continuous-time transfer of the lumping: that
`exp(t L_*) (f ∘ |2·−n|) = (exp(t L_odd) f) ∘ |2·−n|`, which would chain the skeleton statement
to `exp_oddLevelMatrix_square_report` and identify `a_n(t)` with the expected terminal square
under the minimising coupling itself.  The generator identity and the skeleton identity are
proved; the Euler-limit transfer between them is not.

Domain conditions: none beyond the manuscript's own.  The rate `λ` is an arbitrary real
throughout, and nonnegativity is needed only for the lumping, where it fixes which of the two
nearest-drift rates is active.
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

/-- The derivative of a bare exponential of a linear argument. -/
theorem hasDerivAt_expLin (a t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ Real.exp (a * s)) (Real.exp (a * t) * a) t := by
  have h1 : HasDerivAt (fun s : ℝ ↦ a * s) a t := by
    simpa using (hasDerivAt_id t).const_mul a
  exact h1.exp

/-- The derivative of a single exponential term. -/
theorem hasDerivAt_expTerm (a c t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ c * Real.exp (a * s)) (c * a * Real.exp (a * t)) t := by
  have h3 : HasDerivAt (fun s : ℝ ↦ c * Real.exp (a * s)) (c * (Real.exp (a * t) * a)) t :=
    (hasDerivAt_expLin a t).const_mul c
  convert h3 using 1
  ring

/-- The derivative of a level, term by term. -/
theorem hasDerivAt_oddSolution (lam : ℝ) (r : ℕ) (t : ℝ) :
    HasDerivAt (oddSolution lam r)
      (∑ q ∈ Finset.range (r + 1),
        oddRow r q * (-(dexp q) * lam) * Real.exp (-(dexp q) * lam * t)) t := by
  have h : HasDerivAt (∑ q ∈ Finset.range (r + 1),
        fun s : ℝ ↦ oddRow r q * Real.exp (-(dexp q) * lam * s))
      (∑ q ∈ Finset.range (r + 1),
        oddRow r q * (-(dexp q) * lam) * Real.exp (-(dexp q) * lam * t)) t :=
    HasDerivAt.sum fun q _ ↦ hasDerivAt_expTerm (-(dexp q) * lam) (oddRow r q) t
  have hfun : (∑ q ∈ Finset.range (r + 1),
      fun s : ℝ ↦ oddRow r q * Real.exp (-(dexp q) * lam * s)) = oddSolution lam r := by
    funext s
    rw [oddSolution, Finset.sum_apply]
  rwa [hfun] at h

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

/-! ## Uniqueness of the solution -/

/-- **The system (4.6) determines its solution.**  Two families satisfying the three clauses
agree at every level and time, so `a_n` is a determinate function and the endpoint of
DC Corollary 4.3 is a number rather than a description.  The argument is the integrating factor
`e^{λ(2r+3)t}` applied to the difference at each level in turn. -/
theorem oddSystem_unique (lam : ℝ) (a b : ℕ → ℝ → ℝ) (ha0 : ∀ t, a 0 t = 1)
    (hb0 : ∀ t, b 0 t = 1)
    (haD : ∀ r t, HasDerivAt (a (r + 1))
      (lam * (2 * ((r : ℝ) + 1) + 1) * (a r t - a (r + 1) t)) t)
    (hbD : ∀ r t, HasDerivAt (b (r + 1))
      (lam * (2 * ((r : ℝ) + 1) + 1) * (b r t - b (r + 1) t)) t)
    (hai : ∀ r, a (r + 1) 0 = (2 * ((r : ℝ) + 1) + 1) ^ 2)
    (hbi : ∀ r, b (r + 1) 0 = (2 * ((r : ℝ) + 1) + 1) ^ 2) :
    ∀ r t, a r t = b r t := by
  intro r
  induction r with
  | zero =>
    intro t
    rw [ha0, hb0]
  | succ r ih =>
    intro t
    have hg : ∀ s : ℝ, HasDerivAt (fun u : ℝ ↦ (a (r + 1) u - b (r + 1) u)
        * Real.exp (lam * (2 * ((r : ℝ) + 1) + 1) * u)) 0 s := by
      intro s
      have hd : HasDerivAt (fun u : ℝ ↦ a (r + 1) u - b (r + 1) u)
          (lam * (2 * ((r : ℝ) + 1) + 1) * (a r s - a (r + 1) s)
            - lam * (2 * ((r : ℝ) + 1) + 1) * (b r s - b (r + 1) s)) s :=
        (haD r s).sub (hbD r s)
      have hmul := hd.mul (hasDerivAt_expLin (lam * (2 * ((r : ℝ) + 1) + 1)) s)
      convert hmul using 1
      rw [ih s]
      ring
    have hconst := is_const_of_deriv_eq_zero
      (f := fun u : ℝ ↦ (a (r + 1) u - b (r + 1) u)
        * Real.exp (lam * (2 * ((r : ℝ) + 1) + 1) * u))
      (fun s ↦ (hg s).differentiableAt) (fun s ↦ (hg s).deriv) t 0
    have hg0 : (a (r + 1) 0 - b (r + 1) 0)
        * Real.exp (lam * (2 * ((r : ℝ) + 1) + 1) * 0) = 0 := by
      rw [hai r, hbi r]
      ring
    rw [hg0] at hconst
    rcases mul_eq_zero.mp hconst with h | h
    · linarith
    · exact absurd h (Real.exp_ne_zero _)

/-! ## The same system as a finite generator -/

/-- The odd-locus generator on levels `0, …, m`, written in the shape that
`ContinuousTurnoverSemigroup.linearDeathMatrix` uses: level `r` falls to `gridPred m r` at rate
`λ(2r+1)`, and level `0` is absorbing because its own predecessor is itself. -/
def oddLevelMatrix (m : ℕ) (lam : ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun r i ↦ lam * (2 * (((r : ℕ) : ℝ)) + 1)
    * ((if i = gridPred m r then (1 : ℝ) else 0) - (if i = r then (1 : ℝ) else 0))

/-- **The odd-locus generator acts by the scaled down-difference**, which is the right-hand side
of (4.6) read on the level grid. -/
theorem oddLevelMatrix_mulVec (m : ℕ) (lam : ℝ) (v : Fin (m + 1) → ℝ) (r : Fin (m + 1)) :
    (oddLevelMatrix m lam).mulVec v r
      = lam * (2 * (((r : ℕ) : ℝ)) + 1) * (v (gridPred m r) - v r) := by
  have hpt : ∀ i : Fin (m + 1), oddLevelMatrix m lam r i * v i
      = lam * (2 * (((r : ℕ) : ℝ)) + 1) * ((if i = gridPred m r then v i else 0)
        - (if i = r then v i else 0)) := by
    intro i
    simp only [oddLevelMatrix, Matrix.of_apply]
    by_cases h1 : i = gridPred m r
    · by_cases h2 : i = r
      · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2]
        ring
      · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]
        ring
    · by_cases h2 : i = r
      · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
        ring
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
        ring
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl fun i _ ↦ hpt i, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' Finset.univ (gridPred m r) v, Finset.sum_ite_eq' Finset.univ r v,
    if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]

/-! ## The solution as the semigroup of the generator -/

/-- Coefficients past the diagonal vanish. -/
theorem oddRow_eq_zero_of_lt (r q : ℕ) (h : r < q) : oddRow r q = 0 := by
  cases r with
  | zero => rw [oddRow_zero, if_neg (by omega)]
  | succ r =>
    conv_lhs => rw [oddRow]
    simp only [if_neg (show ¬ (q < r + 1) by omega), if_neg (show ¬ (q = r + 1) by omega)]

/-- **Each coefficient column is an eigenvector of the odd-locus generator**, with eigenvalue
the negated decay rate of its own slot.  This is the matching recursion read as an eigenvector
equation, and it is why the solution is a finite combination of exponentials. -/
theorem oddLevelMatrix_eigen (m : ℕ) (lam : ℝ) (q : ℕ) :
    (oddLevelMatrix m lam).mulVec (fun r : Fin (m + 1) ↦ oddRow (r : ℕ) q)
      = (-(dexp q) * lam) • (fun r : Fin (m + 1) ↦ oddRow (r : ℕ) q) := by
  funext r
  rw [oddLevelMatrix_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul]
  rcases Nat.eq_zero_or_pos (r : ℕ) with h0 | hpos
  · have hpred : ((gridPred m r : Fin (m + 1)) : ℕ) = 0 := by
      simp [gridPred, h0]
    rw [hpred, h0, sub_self, mul_zero]
    rcases Nat.eq_zero_or_pos q with hq | hq
    · rw [hq, dexp_zero]
      ring
    · rw [oddRow_eq_zero_of_lt 0 q hq]
      ring
  · obtain ⟨r', hr'⟩ : ∃ r' : ℕ, (r : ℕ) = r' + 1 := ⟨(r : ℕ) - 1, by omega⟩
    have hpred : ((gridPred m r : Fin (m + 1)) : ℕ) = r' := by
      simp [gridPred, hr']
    rw [hpred, hr']
    rcases lt_trichotomy q (r' + 1) with hq | hq | hq
    · have hkey := oddShift_mul r' q hq
      push_cast
      linear_combination (-lam) * hkey
    · rw [hq, oddRow_eq_zero_of_lt r' (r' + 1) (by omega), dexp_succ]
      push_cast
      ring
    · rw [oddRow_eq_zero_of_lt r' q (by omega), oddRow_eq_zero_of_lt (r' + 1) q hq]
      ring

/-- A matrix acts on a finite sum of vectors term by term. -/
theorem mulVec_sum {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (s : Finset ℕ)
    (v : ℕ → Fin N → ℝ) : M.mulVec (∑ q ∈ s, v q) = ∑ q ∈ s, M.mulVec (v q) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.mulVec_add, ih]

/-- The coefficient columns reassemble the initial square report. -/
theorem sum_oddRow_columns (m : ℕ) (r : Fin (m + 1)) :
    ∑ q ∈ Finset.range (m + 1), oddRow (r : ℕ) q = (2 * (((r : ℕ) : ℝ)) + 1) ^ 2 := by
  rw [← sum_oddRow (r : ℕ)]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro q hq
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hq) (by omega))
  · intro q _ hq
    exact oddRow_eq_zero_of_lt (r : ℕ) q (by
      have := Finset.mem_range.not.mp hq
      omega)

/-- **DC Corollary 4.3 as a semigroup identity.**  Running the odd-locus generator for time `t`
on the initial square report `(2r+1)²` produces exactly `a_{2r+1}(t)`.  The proof is the
eigenvector action of `ContinuousTurnoverSemigroup.exp_mulVec_eigen` applied to each coefficient
column, so it goes through the Euler limit rather than through an ODE. -/
theorem exp_oddLevelMatrix_square_report (m : ℕ) (lam t : ℝ) (r : Fin (m + 1)) :
    (NormedSpace.exp ℝ (t • oddLevelMatrix m lam)).mulVec
        (fun r' ↦ (2 * (((r' : ℕ) : ℝ)) + 1) ^ 2) r
      = oddSolution lam (r : ℕ) t := by
  have hinit : (fun r' : Fin (m + 1) ↦ (2 * (((r' : ℕ) : ℝ)) + 1) ^ 2)
      = ∑ q ∈ Finset.range (m + 1), fun r' : Fin (m + 1) ↦ oddRow (r' : ℕ) q := by
    funext r'
    rw [Finset.sum_apply, sum_oddRow_columns m r']
  rw [hinit, mulVec_sum, Finset.sum_apply]
  have hterm : ∀ q ∈ Finset.range (m + 1),
      (NormedSpace.exp ℝ (t • oddLevelMatrix m lam)).mulVec
          (fun r' : Fin (m + 1) ↦ oddRow (r' : ℕ) q) r
        = oddRow (r : ℕ) q * Real.exp (-(dexp q) * lam * t) := by
    intro q _
    rw [exp_mulVec_eigen (oddLevelMatrix m lam) (fun r' : Fin (m + 1) ↦ oddRow (r' : ℕ) q)
      (-(dexp q) * lam) t (oddLevelMatrix_eigen m lam q) r, ← Real.exp_eq_exp_ℝ,
      show t * (-(dexp q) * lam) = -(dexp q) * lam * t from by ring]
    ring
  rw [Finset.sum_congr rfl hterm, oddSolution]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro q hq
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hq) (by omega))
  · intro q _ hq
    rw [oddRow_eq_zero_of_lt (r : ℕ) q (by
      have := Finset.mem_range.not.mp hq
      omega), zero_mul]

/-! ## The odd-level generator as a lumping of the count generator -/

/-- The odd aggregate report `|2k − n|` at count `k`, for an odd cohort size `n = 2c + 1`. -/
def oddAggregate (c : ℕ) (k : ℤ) : ℤ :=
  |2 * k - ((2 * c + 1 : ℕ) : ℤ)|

/-- The odd-level generator read on `ℤ`: `|M|` falls by two at rate `λ|M|`, and `M = 1` is
absorbing because its truncated predecessor is itself. -/
def oddGenZ (lam : ℝ) (g : ℤ → ℝ) (M : ℤ) : ℝ :=
  lam * (M : ℝ) * (g (max (M - 2) 1) - g M)

/-- The aggregate is never zero or two, because `2k − n` is odd. -/
theorem oddAggregate_cases (c : ℕ) (k : ℤ) :
    oddAggregate c k = 1 ∨ 3 ≤ oddAggregate c k := by
  rw [oddAggregate]
  rcases abs_cases (2 * k - ((2 * c + 1 : ℕ) : ℤ)) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> omega

/-- The aggregate one step up is the truncated predecessor of the aggregate, when the count is
below the balance point. -/
theorem oddAggregate_succ_of_lt (c : ℕ) (k : ℤ) (h : 2 * k < ((2 * c + 1 : ℕ) : ℤ)) :
    oddAggregate c (k + 1) = max (oddAggregate c k - 2) 1 := by
  have habs : oddAggregate c k = ((2 * c + 1 : ℕ) : ℤ) - 2 * k := by
    rw [oddAggregate, abs_sub_comm, abs_of_pos (by omega)]
  rw [habs, oddAggregate]
  rcases (by omega : ((2 * c + 1 : ℕ) : ℤ) - 2 * k = 1
      ∨ 3 ≤ ((2 * c + 1 : ℕ) : ℤ) - 2 * k) with h1 | h3
  · rw [abs_of_pos (by omega), h1]
    norm_num
    omega
  · rw [abs_of_neg (by omega), max_eq_left (by omega)]
    omega

/-- The aggregate one step down is the truncated predecessor of the aggregate, when the count is
above the balance point. -/
theorem oddAggregate_pred_of_gt (c : ℕ) (k : ℤ) (h : ((2 * c + 1 : ℕ) : ℤ) < 2 * k) :
    oddAggregate c (k - 1) = max (oddAggregate c k - 2) 1 := by
  have habs : oddAggregate c k = 2 * k - ((2 * c + 1 : ℕ) : ℤ) := by
    rw [oddAggregate, abs_of_pos (by omega)]
  rw [habs, oddAggregate]
  rcases (by omega : 2 * k - ((2 * c + 1 : ℕ) : ℤ) = 1
      ∨ 3 ≤ 2 * k - ((2 * c + 1 : ℕ) : ℤ)) with h1 | h3
  · rw [abs_of_neg (by omega), h1]
    norm_num
    omega
  · rw [abs_of_pos (by omega), max_eq_left (by omega)]
    omega

/-- **The odd-level generator is the lumping of the nearest-drift count generator.**  At
symmetric rates the count drift is `b(k) = λ(n − 2k)`, so the nearest-drift chain always moves
one step toward the balance point, and the aggregate `|2k − n|` therefore falls by exactly two
at rate `λ|2k − n|`.  At `|2k − n| = 1` the count still moves but the aggregate does not, which
is the manuscript's remark that the sign can switch while the square stays one. -/
theorem nearestDriftGen_lump (c : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) (g : ℤ → ℝ) (k : ℤ) :
    ConvexOrderCoupling.nearestDriftGen (2 * c + 1) lam lam
        (fun j ↦ g (oddAggregate c j)) k
      = oddGenZ lam g (oddAggregate c k) := by
  have hdrift : ConvexOrderCoupling.countDrift (2 * c + 1) lam lam k
      = lam * (((((2 * c + 1 : ℕ) : ℤ) - 2 * k : ℤ)) : ℝ) := by
    rw [ConvexOrderCoupling.countDrift]
    push_cast
    ring
  rcases lt_trichotomy (2 * k) (((2 * c + 1 : ℕ) : ℤ)) with hlt | heq | hgt
  · have hpos : (0 : ℝ) < (((((2 * c + 1 : ℕ) : ℤ) - 2 * k : ℤ)) : ℝ) := by
      have : (0 : ℤ) < ((2 * c + 1 : ℕ) : ℤ) - 2 * k := by omega
      exact_mod_cast this
    have habs : oddAggregate c k = ((2 * c + 1 : ℕ) : ℤ) - 2 * k := by
      rw [oddAggregate, abs_sub_comm, abs_of_pos (by omega)]
    rw [ConvexOrderCoupling.nearestDriftGen, ConvexOrderCoupling.upRate,
      ConvexOrderCoupling.downRate, hdrift,
      max_eq_left (by positivity : (0 : ℝ) ≤ lam * _),
      max_eq_right (by nlinarith : -(lam * (((((2 * c + 1 : ℕ) : ℤ) - 2 * k : ℤ)) : ℝ)) ≤ 0),
      oddGenZ, oddAggregate_succ_of_lt c k hlt, habs]
    push_cast
    ring
  · exfalso
    omega
  · have hneg : (((((2 * c + 1 : ℕ) : ℤ) - 2 * k : ℤ)) : ℝ) < 0 := by
      have : ((2 * c + 1 : ℕ) : ℤ) - 2 * k < 0 := by omega
      exact_mod_cast this
    have habs : oddAggregate c k = 2 * k - ((2 * c + 1 : ℕ) : ℤ) := by
      rw [oddAggregate, abs_of_pos (by omega)]
    rw [ConvexOrderCoupling.nearestDriftGen, ConvexOrderCoupling.upRate,
      ConvexOrderCoupling.downRate, hdrift,
      max_eq_right (by nlinarith : lam * (((((2 * c + 1 : ℕ) : ℤ) - 2 * k : ℤ)) : ℝ) ≤ 0),
      max_eq_left (by nlinarith : (0 : ℝ) ≤ -(lam * (((((2 * c + 1 : ℕ) : ℤ) - 2 * k : ℤ)) : ℝ))),
      oddGenZ, oddAggregate_pred_of_gt c k hgt, habs]
    push_cast
    ring

/-! ## The lumping at every skeleton horizon -/

/-- One skeleton step of the odd-level generator. -/
def oddStepZ (lam tau : ℝ) (g : ℤ → ℝ) : ℤ → ℝ :=
  fun M ↦ g M + tau * oddGenZ lam g M

/-- **One skeleton step lumps.** -/
theorem driftStep_lump (c : ℕ) (lam tau : ℝ) (hlam : 0 ≤ lam) (g : ℤ → ℝ) (k : ℤ) :
    ConvexOrderCoupling.driftStep (2 * c + 1) lam lam tau (fun j ↦ g (oddAggregate c j)) k
      = oddStepZ lam tau g (oddAggregate c k) := by
  rw [ConvexOrderCoupling.driftStep, oddStepZ, nearestDriftGen_lump c lam hlam g k]

/-- **The lumping survives every horizon.**  Running the nearest-drift count chain on a report
that depends only on the aggregate is the same as running the odd-level chain on that report.
This is what ties DC Corollary 4.3's system back to the minimising coupling: the aggregate
report of the count chain is the odd-level chain. -/
theorem driftStep_iterate_lump (c : ℕ) (lam tau : ℝ) (hlam : 0 ≤ lam) (g : ℤ → ℝ) (m : ℕ) :
    ∀ k : ℤ, (ConvexOrderCoupling.driftStep (2 * c + 1) lam lam tau)^[m]
        (fun j ↦ g (oddAggregate c j)) k
      = (oddStepZ lam tau)^[m] g (oddAggregate c k) := by
  induction m with
  | zero =>
    intro k
    simp
  | succ m ih =>
    intro k
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hfun : (ConvexOrderCoupling.driftStep (2 * c + 1) lam lam tau)^[m]
        (fun j ↦ g (oddAggregate c j))
        = fun j ↦ ((oddStepZ lam tau)^[m] g) (oddAggregate c j) := by
      funext j
      exact ih j
    rw [hfun, driftStep_lump c lam tau hlam ((oddStepZ lam tau)^[m] g) k]

/-! ## The lumping as a matrix intertwiner -/

/-- The odd level of a count on the grid: `k ↦ (|2k − n| − 1)/2` for `n = 2c + 1`. -/
def aggLevel (c : ℕ) (k : Fin (2 * c + 1 + 1)) : Fin (c + 1) :=
  ⟨if (k : ℕ) ≤ c then c - (k : ℕ) else (k : ℕ) - c - 1, by
    have := k.isLt
    split <;> omega⟩

/-- The level below the balance point. -/
theorem aggLevel_of_le (c : ℕ) (k : Fin (2 * c + 1 + 1)) (h : (k : ℕ) ≤ c) :
    ((aggLevel c k : Fin (c + 1)) : ℕ) = c - (k : ℕ) := by
  simp [aggLevel, h]

/-- The level above the balance point. -/
theorem aggLevel_of_gt (c : ℕ) (k : Fin (2 * c + 1 + 1)) (h : ¬ ((k : ℕ) ≤ c)) :
    ((aggLevel c k : Fin (c + 1)) : ℕ) = (k : ℕ) - c - 1 := by
  simp [aggLevel, h]

/-- Stepping the count up below the balance point steps the level down. -/
theorem aggLevel_gridSucc (c : ℕ) (k : Fin (2 * c + 1 + 1)) (h : (k : ℕ) ≤ c) :
    aggLevel c (ContinuousTurnoverSemigroup.gridSucc (2 * c + 1) k)
      = ContinuousTurnoverSemigroup.gridPred c (aggLevel c k) := by
  apply Fin.ext
  have hk := k.isLt
  simp only [aggLevel, ContinuousTurnoverSemigroup.gridSucc,
    ContinuousTurnoverSemigroup.gridPred]
  split_ifs <;> omega

/-- Stepping the count down above the balance point steps the level down. -/
theorem aggLevel_gridPred (c : ℕ) (k : Fin (2 * c + 1 + 1)) (h : ¬ ((k : ℕ) ≤ c)) :
    aggLevel c (ContinuousTurnoverSemigroup.gridPred (2 * c + 1) k)
      = ContinuousTurnoverSemigroup.gridPred c (aggLevel c k) := by
  apply Fin.ext
  have hk := k.isLt
  simp only [aggLevel, ContinuousTurnoverSemigroup.gridPred]
  split_ifs <;> omega

/-- The pullback matrix of the lumping: row `k` selects the level of `k`. -/
def pullbackMatrix (c : ℕ) : Matrix (Fin (2 * c + 1 + 1)) (Fin (c + 1)) ℝ :=
  Matrix.of fun k j ↦ if aggLevel c k = j then (1 : ℝ) else 0

/-- The pullback matrix reads a level report at the level of the count. -/
theorem pullbackMatrix_mulVec (c : ℕ) (v : Fin (c + 1) → ℝ) (k : Fin (2 * c + 1 + 1)) :
    (pullbackMatrix c).mulVec v k = v (aggLevel c k) := by
  simp only [Matrix.mulVec, dotProduct, pullbackMatrix, Matrix.of_apply, ite_mul, one_mul,
    zero_mul]
  rw [Finset.sum_ite_eq Finset.univ (aggLevel c k) v, if_pos (Finset.mem_univ _)]

/-- The nearest-drift matrix in grid form, with the clamped neighbours made explicit. -/
theorem nearestDriftMatrix_mulVec_grid (n : ℕ) (α β : ℝ) (v : Fin (n + 1) → ℝ)
    (k : Fin (n + 1)) :
    (ContinuousTurnoverSemigroup.nearestDriftMatrix n α β).mulVec v k
      = ConvexOrderCoupling.upRate n α β ((k : ℕ) : ℤ)
          * (v (ContinuousTurnoverSemigroup.gridSucc n k) - v k)
        + ConvexOrderCoupling.downRate n α β ((k : ℕ) : ℤ)
          * (v (ContinuousTurnoverSemigroup.gridPred n k) - v k) := by
  rw [ContinuousTurnoverSemigroup.nearestDriftMatrix_mulVec,
    ConvexOrderCoupling.nearestDriftGen, ContinuousTurnoverSemigroup.gridEmbed_succ,
    ContinuousTurnoverSemigroup.gridEmbed_pred, ContinuousTurnoverSemigroup.gridEmbed_coe]

/-- The count drift at symmetric rates, on the grid. -/
theorem countDrift_grid (c : ℕ) (lam : ℝ) (k : Fin (2 * c + 1 + 1)) :
    ConvexOrderCoupling.countDrift (2 * c + 1) lam lam ((k : ℕ) : ℤ)
      = lam * ((2 * (c : ℝ) + 1) - 2 * ((k : ℕ) : ℝ)) := by
  rw [ConvexOrderCoupling.countDrift]
  push_cast
  ring

/-- Below the balance point the whole drift is upward, at the level's own rate. -/
theorem upRate_grid_le (c : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) (k : Fin (2 * c + 1 + 1))
    (h : (k : ℕ) ≤ c) :
    ConvexOrderCoupling.upRate (2 * c + 1) lam lam ((k : ℕ) : ℤ)
      = lam * (2 * (((aggLevel c k : Fin (c + 1)) : ℕ) : ℝ) + 1) := by
  have hcast : (((c - (k : ℕ) : ℕ)) : ℝ) = (c : ℝ) - ((k : ℕ) : ℝ) := by
    exact Nat.cast_sub h
  have hval : lam * ((2 * (c : ℝ) + 1) - 2 * ((k : ℕ) : ℝ))
      = lam * (2 * (((aggLevel c k : Fin (c + 1)) : ℕ) : ℝ) + 1) := by
    rw [aggLevel_of_le c k h, hcast]
    ring
  have hnn : 0 ≤ lam * ((2 * (c : ℝ) + 1) - 2 * ((k : ℕ) : ℝ)) := by
    have : ((k : ℕ) : ℝ) ≤ (c : ℝ) := by exact_mod_cast h
    nlinarith
  rw [ConvexOrderCoupling.upRate, countDrift_grid, max_eq_left hnn, hval]

/-- Below the balance point there is no downward rate. -/
theorem downRate_grid_le (c : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) (k : Fin (2 * c + 1 + 1))
    (h : (k : ℕ) ≤ c) :
    ConvexOrderCoupling.downRate (2 * c + 1) lam lam ((k : ℕ) : ℤ) = 0 := by
  have hnn : 0 ≤ lam * ((2 * (c : ℝ) + 1) - 2 * ((k : ℕ) : ℝ)) := by
    have : ((k : ℕ) : ℝ) ≤ (c : ℝ) := by exact_mod_cast h
    nlinarith
  rw [ConvexOrderCoupling.downRate, countDrift_grid, max_eq_right (by linarith)]

/-- Above the balance point the whole drift is downward, at the level's own rate. -/
theorem downRate_grid_gt (c : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) (k : Fin (2 * c + 1 + 1))
    (h : ¬ ((k : ℕ) ≤ c)) :
    ConvexOrderCoupling.downRate (2 * c + 1) lam lam ((k : ℕ) : ℤ)
      = lam * (2 * (((aggLevel c k : Fin (c + 1)) : ℕ) : ℝ) + 1) := by
  have hle : c + 1 ≤ (k : ℕ) := by omega
  have hcast : ((((k : ℕ) - c - 1 : ℕ)) : ℝ) = ((k : ℕ) : ℝ) - (c : ℝ) - 1 := by
    have h1 : (((k : ℕ) - c - 1 : ℕ) : ℝ) = (((k : ℕ) - c : ℕ) : ℝ) - 1 := by
      have : 1 ≤ (k : ℕ) - c := by omega
      exact Nat.cast_sub this
    have h2 : ((((k : ℕ) - c : ℕ)) : ℝ) = ((k : ℕ) : ℝ) - (c : ℝ) := by
      exact Nat.cast_sub (by omega : c ≤ (k : ℕ))
    rw [h1, h2]
  have hval : -(lam * ((2 * (c : ℝ) + 1) - 2 * ((k : ℕ) : ℝ)))
      = lam * (2 * (((aggLevel c k : Fin (c + 1)) : ℕ) : ℝ) + 1) := by
    rw [aggLevel_of_gt c k h, hcast]
    ring
  have hnn : 0 ≤ -(lam * ((2 * (c : ℝ) + 1) - 2 * ((k : ℕ) : ℝ))) := by
    have : (c : ℝ) + 1 ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hle
    nlinarith
  rw [ConvexOrderCoupling.downRate, countDrift_grid, max_eq_left hnn, hval]

/-- Above the balance point there is no upward rate. -/
theorem upRate_grid_gt (c : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) (k : Fin (2 * c + 1 + 1))
    (h : ¬ ((k : ℕ) ≤ c)) :
    ConvexOrderCoupling.upRate (2 * c + 1) lam lam ((k : ℕ) : ℤ) = 0 := by
  have hle : c + 1 ≤ (k : ℕ) := by omega
  have hnn : 0 ≤ -(lam * ((2 * (c : ℝ) + 1) - 2 * ((k : ℕ) : ℝ))) := by
    have : (c : ℝ) + 1 ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hle
    nlinarith
  rw [ConvexOrderCoupling.upRate, countDrift_grid, max_eq_right (by linarith)]

/-- **The lumping as an intertwining, in acting form.** -/
theorem nearestDrift_lump_mulVec (c : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) (v : Fin (c + 1) → ℝ)
    (k : Fin (2 * c + 1 + 1)) :
    (ContinuousTurnoverSemigroup.nearestDriftMatrix (2 * c + 1) lam lam).mulVec
        ((pullbackMatrix c).mulVec v) k
      = (pullbackMatrix c).mulVec ((oddLevelMatrix c lam).mulVec v) k := by
  rw [nearestDriftMatrix_mulVec_grid]
  simp only [pullbackMatrix_mulVec]
  rw [oddLevelMatrix_mulVec]
  by_cases h : (k : ℕ) ≤ c
  · rw [upRate_grid_le c lam hlam k h, downRate_grid_le c lam hlam k h,
      aggLevel_gridSucc c k h]
    ring
  · rw [upRate_grid_gt c lam hlam k h, downRate_grid_gt c lam hlam k h,
      aggLevel_gridPred c k h]
    ring

/-- **The lumping as a matrix intertwiner.** -/
theorem nearestDrift_pullback_intertwine (c : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) :
    ContinuousTurnoverSemigroup.nearestDriftMatrix (2 * c + 1) lam lam * pullbackMatrix c
      = pullbackMatrix c * oddLevelMatrix c lam := by
  ext k j
  have hL : ((ContinuousTurnoverSemigroup.nearestDriftMatrix (2 * c + 1) lam lam
      * pullbackMatrix c).mulVec (Pi.single j 1)) k
      = (ContinuousTurnoverSemigroup.nearestDriftMatrix (2 * c + 1) lam lam).mulVec
          ((pullbackMatrix c).mulVec (Pi.single j 1)) k := by
    rw [Matrix.mulVec_mulVec]
  have hR : ((pullbackMatrix c * oddLevelMatrix c lam).mulVec (Pi.single j 1)) k
      = (pullbackMatrix c).mulVec ((oddLevelMatrix c lam).mulVec (Pi.single j 1)) k := by
    rw [Matrix.mulVec_mulVec]
  have hmain := nearestDrift_lump_mulVec c lam hlam (Pi.single j 1) k
  rw [← hL, ← hR] at hmain
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hmain
  simpa [Matrix.transpose_apply] using hmain

/-! ## The transfer to the semigroups -/

/-- An intertwining survives powers. -/
theorem pow_intertwine {N P : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (B : Matrix (Fin P) (Fin P) ℝ)
    (Q : Matrix (Fin N) (Fin P) ℝ) (h : A * Q = Q * B) (r : ℕ) : A ^ r * Q = Q * B ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

/-- An intertwining survives the Euler approximants. -/
theorem euler_intertwine {N P : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (B : Matrix (Fin P) (Fin P) ℝ) (Q : Matrix (Fin N) (Fin P) ℝ) (h : A * Q = Q * B)
    (tau : ℝ) (r : ℕ) : (1 + tau • A) ^ r * Q = Q * (1 + tau • B) ^ r := by
  refine pow_intertwine _ _ _ ?_ r
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, h]

/-- Multiplying on the right by a fixed matrix and reading one entry is linear. -/
def mulRightEntry {N P : ℕ} (Q : Matrix (Fin N) (Fin P) ℝ) (k : Fin N) (j : Fin P) :
    Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ where
  toFun M := (M * Q) k j
  map_add' M M' := by simp [Matrix.add_mul]
  map_smul' a M := by simp [Matrix.smul_mul]

/-- Multiplying on the left by a fixed matrix and reading one entry is linear. -/
def mulLeftEntry {N P : ℕ} (Q : Matrix (Fin N) (Fin P) ℝ) (k : Fin N) (j : Fin P) :
    Matrix (Fin P) (Fin P) ℝ →ₗ[ℝ] ℝ where
  toFun M := (Q * M) k j
  map_add' M M' := by simp [Matrix.mul_add]
  map_smul' a M := by simp [Matrix.mul_smul]

/-- **An intertwining passes to the semigroups**, through the same Euler limit that
`Descent.Portability.ContinuousTurnoverSemigroup` uses to build its exponential. -/
theorem exp_intertwine {N P : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (B : Matrix (Fin P) (Fin P) ℝ)
    (Q : Matrix (Fin N) (Fin P) ℝ) (h : A * Q = Q * B) :
    NormedSpace.exp ℝ A * Q = Q * NormedSpace.exp ℝ B := by
  ext k j
  have hcL : Continuous (mulRightEntry Q k j) :=
    (mulRightEntry Q k j).continuous_of_finiteDimensional
  have hcR : Continuous (mulLeftEntry Q k j) :=
    (mulLeftEntry Q k j).continuous_of_finiteDimensional
  have hA := (hcL.tendsto (NormedSpace.exp ℝ A)).comp
    (BanachEulerExponential.euler_tends_exp A)
  have hB := (hcR.tendsto (NormedSpace.exp ℝ B)).comp
    (BanachEulerExponential.euler_tends_exp B)
  have heq : ∀ r : ℕ, (mulRightEntry Q k j) ((1 + (r : ℝ)⁻¹ • A) ^ r)
      = (mulLeftEntry Q k j) ((1 + (r : ℝ)⁻¹ • B) ^ r) := by
    intro r
    show ((1 + (r : ℝ)⁻¹ • A) ^ r * Q) k j = (Q * (1 + (r : ℝ)⁻¹ • B) ^ r) k j
    rw [euler_intertwine A B Q h ((r : ℝ)⁻¹) r]
  exact tendsto_nhds_unique (Filter.Tendsto.congr heq hA) hB

/-- **DC Corollary 4.3 for the minimising count chain, in continuous time.**  Running the
nearest-drift count semigroup at symmetric rates on the squared aggregate report `(2k − n)²`
produces exactly `a_n(t)` at the aggregate's own level.  The chain is: the lumping intertwines
the two generators, the intertwining passes to the semigroups through the Euler limit, and
`exp_oddLevelMatrix_square_report` evaluates the odd-level side. -/
theorem exp_nearestDrift_square_report (c : ℕ) (lam t : ℝ) (hlam : 0 ≤ lam)
    (k : Fin (2 * c + 1 + 1)) :
    (NormedSpace.exp ℝ
        (t • ContinuousTurnoverSemigroup.nearestDriftMatrix (2 * c + 1) lam lam)).mulVec
        (fun k' ↦ (2 * (((aggLevel c k' : Fin (c + 1)) : ℕ) : ℝ) + 1) ^ 2) k
      = oddSolution lam ((aggLevel c k : Fin (c + 1)) : ℕ) t := by
  have hint : (t • ContinuousTurnoverSemigroup.nearestDriftMatrix (2 * c + 1) lam lam)
      * pullbackMatrix c = pullbackMatrix c * (t • oddLevelMatrix c lam) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, nearestDrift_pullback_intertwine c lam hlam]
  have hexp := exp_intertwine _ _ _ hint
  have hpull : (fun k' : Fin (2 * c + 1 + 1) ↦
      (2 * (((aggLevel c k' : Fin (c + 1)) : ℕ) : ℝ) + 1) ^ 2)
      = (pullbackMatrix c).mulVec (fun r : Fin (c + 1) ↦ (2 * ((r : ℕ) : ℝ) + 1) ^ 2) := by
    funext k'
    rw [pullbackMatrix_mulVec]
  rw [hpull, Matrix.mulVec_mulVec, hexp, ← Matrix.mulVec_mulVec, pullbackMatrix_mulVec,
    exp_oddLevelMatrix_square_report]

end

end Descent.Portability.OddLocusReportSolutions
