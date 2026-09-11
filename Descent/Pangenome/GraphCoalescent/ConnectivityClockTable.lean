/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The exact connectivity-clock table

Section 6 of the hidden-lineage clock note computes the reported connection clock of a pangenome
graph through a partition-lattice cumulant and tabulates five exact examples.  This file checks
every row of that table by rational arithmetic: the connectivity cumulant `C_c(z)` of the fiber
sizes `c = (1,2), (1,3), (2,2), (1,1,2), (2,2,2)` and the mean reported connection time
`E τ_q = 2/3, 1/2, 7/18, 17/18, 92/225`, together with the observation the note draws from
them: the fiber sizes `(1,3)` and `(2,2)` have the same sample size `n = 4` and the same width
`w = 2` but different means, so the width does not determine the clock.

The definitions are transcriptions of the note's formulas.  `lahPolynomial m` is (D1),
`A_m(z) = ∑_{j=1}^m (m!/j!) C(m-1, j-1) z^j`.  `connectivityCumulantTwo` and
`connectivityCumulantThree` are (D2) for two and three fibers, written out over the partitions of
the fibers with the Möbius coefficients `μ(σ, ⊤) = (-1)^{|σ|-1} (|σ|-1)!`: for two fibers the top
partition with coefficient `1` and the bottom one with `-1`; for three fibers the top partition
with `1`, the three two-block partitions with `-1` each, and the bottom partition with `2`.
`rankedWeight n k` is `a_{n,k}` of (D4), `connectedByLevel` is `F_k` of (D5), `firstConnectionLaw`
is `p_b` of (D6), and `meanConnectionTime` is (D8), `E τ_q = 2 ∑_b p_b / b - 2/n`.

The corpus modules of the note's Theorem D, `LahWeights` and `ConnectivityCumulant` for (D1)-(D3)
and `RankedHistoryLaw` and `ReportedConnectionClock` for (D4)-(D9), were not yet on main when this
file was written.  When they land, these local transcriptions are to be replaced by their
definitions and the rows restated against them; the arithmetic below does not change.

Scope.  Nothing here proves (D3), the combinatorial meaning of the cumulant, or (D4)-(D8), the
ranked-history law and the first-connection law; those are the business of the modules named
above.  This file evaluates the formulas at the tabulated fiber sizes.

## Empirical status

None.  The bodies here are rational arithmetic on explicit polynomials and finite sums, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.ConnectivityClockTable

open Polynomial

noncomputable section

/-! ## The formulas of Theorem D -/

/-- The coefficient `(m!/j!) C(m-1, j-1)` of `z^j` in the Lah polynomial (D1). -/
def lahCoefficient (m j : ℕ) : ℚ :=
  (m.factorial : ℚ) / (j.factorial : ℚ) * ((m - 1).choose (j - 1) : ℚ)

/-- The Lah polynomial (D1), `A_m(z) = ∑_{j=1}^m (m!/j!) C(m-1, j-1) z^j`: partitions of `m`
individuals into `j` blocks weighted by the product of the block-size factorials. -/
def lahPolynomial (m : ℕ) : ℚ[X] :=
  ∑ i ∈ Finset.range m, C (lahCoefficient m (i + 1)) * X ^ (i + 1)

/-- The connectivity cumulant (D2) of two fibers of sizes `c₁` and `c₂`: the top partition of the
fibers with Möbius coefficient `1` and the bottom partition with `-1`. -/
def connectivityCumulantTwo (c₁ c₂ : ℕ) : ℚ[X] :=
  lahPolynomial (c₁ + c₂) - lahPolynomial c₁ * lahPolynomial c₂

/-- The connectivity cumulant (D2) of three fibers of sizes `c₁`, `c₂` and `c₃`: the top partition
with Möbius coefficient `1`, the three two-block partitions with `-1` each, and the bottom
partition with `2`. -/
def connectivityCumulantThree (c₁ c₂ c₃ : ℕ) : ℚ[X] :=
  lahPolynomial (c₁ + c₂ + c₃) -
    (lahPolynomial (c₁ + c₂) * lahPolynomial c₃ + lahPolynomial (c₁ + c₃) * lahPolynomial c₂ +
      lahPolynomial (c₂ + c₃) * lahPolynomial c₁) +
    2 * (lahPolynomial c₁ * lahPolynomial c₂ * lahPolynomial c₃)

/-- The ranked-history weight `a_{n,k} = (n-k)! k! (k-1)! / (n! (n-1)!)` of (D4). -/
def rankedWeight (n k : ℕ) : ℚ :=
  ((n - k).factorial * k.factorial * (k - 1).factorial : ℚ) /
    ((n.factorial : ℚ) * ((n - 1).factorial : ℚ))

/-- The probability `F_k = a_{n,k} [z^k] C_c(z)` of (D5) that the report is connected by the time
the genealogy reaches `k` blocks. -/
def connectedByLevel (cumulant : ℚ[X]) (n k : ℕ) : ℚ :=
  rankedWeight n k * cumulant.coeff k

/-- The law `p_b = F_b - F_{b+1}` of (D6) of the number of true lineages right after the first
reported connection. -/
def firstConnectionLaw (cumulant : ℚ[X]) (n b : ℕ) : ℚ :=
  connectedByLevel cumulant n b - connectedByLevel cumulant n (b + 1)

/-- The mean reported connection time (D8), `E τ_q = 2 ∑_{b=1}^{n-w+1} p_b / b - 2/n`. -/
def meanConnectionTime (cumulant : ℚ[X]) (n w : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range (n - w + 1), firstConnectionLaw cumulant n (i + 1) / ((i : ℚ) + 1) -
    2 / (n : ℚ)

/-! ## The Lah polynomials the table needs -/

/-- `A_1(z) = z`. -/
theorem lahPolynomial_one : lahPolynomial 1 = X := by
  simp [lahPolynomial, lahCoefficient]

/-- `A_2(z) = 2z + z^2`. -/
theorem lahPolynomial_two : lahPolynomial 2 = 2 * X + X ^ 2 := by
  simp only [lahPolynomial, lahCoefficient, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial, Nat.choose]

/-- `A_3(z) = 6z + 6z^2 + z^3`. -/
theorem lahPolynomial_three : lahPolynomial 3 = 6 * X + 6 * X ^ 2 + X ^ 3 := by
  simp only [lahPolynomial, lahCoefficient, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial, Nat.choose]

/-- `A_4(z) = 24z + 36z^2 + 12z^3 + z^4`. -/
theorem lahPolynomial_four : lahPolynomial 4 = 24 * X + 36 * X ^ 2 + 12 * X ^ 3 + X ^ 4 := by
  simp only [lahPolynomial, lahCoefficient, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial, Nat.choose]

/-- `A_6(z) = 720z + 1800z^2 + 1200z^3 + 300z^4 + 30z^5 + z^6`. -/
theorem lahPolynomial_six :
    lahPolynomial 6 = 720 * X + 1800 * X ^ 2 + 1200 * X ^ 3 + 300 * X ^ 4 + 30 * X ^ 5 + X ^ 6 := by
  simp only [lahPolynomial, lahCoefficient, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial, Nat.choose]

/-! ## The connectivity cumulants of the table -/

/-- `C_{(1,2)}(z) = 6z + 4z^2`. -/
theorem connectivityCumulant_one_two : connectivityCumulantTwo 1 2 = 6 * X + 4 * X ^ 2 := by
  rw [connectivityCumulantTwo, show (1 + 2 : ℕ) = 3 from rfl, lahPolynomial_one,
    lahPolynomial_two, lahPolynomial_three]
  ring

/-- `C_{(1,3)}(z) = 24z + 30z^2 + 6z^3`. -/
theorem connectivityCumulant_one_three :
    connectivityCumulantTwo 1 3 = 24 * X + 30 * X ^ 2 + 6 * X ^ 3 := by
  rw [connectivityCumulantTwo, show (1 + 3 : ℕ) = 4 from rfl, lahPolynomial_one,
    lahPolynomial_three, lahPolynomial_four]
  ring

/-- `C_{(2,2)}(z) = 24z + 32z^2 + 8z^3`. -/
theorem connectivityCumulant_two_two :
    connectivityCumulantTwo 2 2 = 24 * X + 32 * X ^ 2 + 8 * X ^ 3 := by
  rw [connectivityCumulantTwo, show (2 + 2 : ℕ) = 4 from rfl, lahPolynomial_two,
    lahPolynomial_four]
  ring

/-- `C_{(1,1,2)}(z) = 24z + 20z^2`. -/
theorem connectivityCumulant_one_one_two :
    connectivityCumulantThree 1 1 2 = 24 * X + 20 * X ^ 2 := by
  rw [connectivityCumulantThree, show (1 + 1 + 2 : ℕ) = 4 from rfl, show (1 + 1 : ℕ) = 2 from rfl,
    show (1 + 2 : ℕ) = 3 from rfl, lahPolynomial_one, lahPolynomial_two, lahPolynomial_three,
    lahPolynomial_four]
  ring

/-- `C_{(2,2,2)}(z) = 720z + 1656z^2 + 928z^3 + 144z^4`. -/
theorem connectivityCumulant_two_two_two :
    connectivityCumulantThree 2 2 2 = 720 * X + 1656 * X ^ 2 + 928 * X ^ 3 + 144 * X ^ 4 := by
  rw [connectivityCumulantThree, show (2 + 2 + 2 : ℕ) = 6 from rfl, show (2 + 2 : ℕ) = 4 from rfl,
    lahPolynomial_two, lahPolynomial_four, lahPolynomial_six]
  ring

/-! ## The mean reported connection times of the table -/

/-- For fibers of sizes `(1,2)`, `E τ_q = 2/3`. -/
theorem meanConnectionTime_one_two :
    meanConnectionTime (connectivityCumulantTwo 1 2) 3 2 = 2 / 3 := by
  rw [connectivityCumulant_one_two]
  norm_num [meanConnectionTime, firstConnectionLaw, connectedByLevel, rankedWeight,
    Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_X_pow, Nat.factorial]

/-- For fibers of sizes `(1,3)`, `E τ_q = 1/2`. -/
theorem meanConnectionTime_one_three :
    meanConnectionTime (connectivityCumulantTwo 1 3) 4 2 = 1 / 2 := by
  rw [connectivityCumulant_one_three]
  norm_num [meanConnectionTime, firstConnectionLaw, connectedByLevel, rankedWeight,
    Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_X_pow, Nat.factorial]

/-- For fibers of sizes `(2,2)`, `E τ_q = 7/18`. -/
theorem meanConnectionTime_two_two :
    meanConnectionTime (connectivityCumulantTwo 2 2) 4 2 = 7 / 18 := by
  rw [connectivityCumulant_two_two]
  norm_num [meanConnectionTime, firstConnectionLaw, connectedByLevel, rankedWeight,
    Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_X_pow, Nat.factorial]

/-- For fibers of sizes `(1,1,2)`, `E τ_q = 17/18`. -/
theorem meanConnectionTime_one_one_two :
    meanConnectionTime (connectivityCumulantThree 1 1 2) 4 3 = 17 / 18 := by
  rw [connectivityCumulant_one_one_two]
  norm_num [meanConnectionTime, firstConnectionLaw, connectedByLevel, rankedWeight,
    Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_X_pow, Nat.factorial]

/-- For fibers of sizes `(2,2,2)`, `E τ_q = 92/225`. -/
theorem meanConnectionTime_two_two_two :
    meanConnectionTime (connectivityCumulantThree 2 2 2) 6 3 = 92 / 225 := by
  rw [connectivityCumulant_two_two_two]
  norm_num [meanConnectionTime, firstConnectionLaw, connectedByLevel, rankedWeight,
    Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_X_pow, Nat.factorial]

/-- **The width does not determine the clock.**  The fiber sizes `(1,3)` and `(2,2)` give the same
sample size `n = 4` and the same width `w = 2`, but their mean reported connection times are `1/2`
and `7/18`. -/
theorem meanConnectionTime_one_three_ne_two_two :
    1 + 3 = 2 + 2 ∧
      meanConnectionTime (connectivityCumulantTwo 1 3) 4 2 ≠
        meanConnectionTime (connectivityCumulantTwo 2 2) 4 2 := by
  refine ⟨rfl, ?_⟩
  rw [meanConnectionTime_one_three, meanConnectionTime_two_two]
  norm_num

end

end Descent.Pangenome.GraphCoalescent.ConnectivityClockTable
