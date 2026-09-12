/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Descent.Pangenome.GraphCoalescent.ConnectivityCumulant
import Mathlib.Tactic

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The exact connectivity-clock table

Section 6 of the hidden-lineage clock note computes the reported connection clock of a pangenome
graph through a partition-lattice cumulant and tabulates five exact examples.  This file checks
every row of that table: the connectivity cumulant `C_c(z)` of the fiber sizes
`c = (1,2), (1,3), (2,2), (1,1,2), (2,2,2)` and the mean reported connection time
`E τ_q = 2/3, 1/2, 7/18, 17/18, 92/225`, together with the observation the note draws from
them: the fiber sizes `(1,3)` and `(2,2)` have the same sample size `n = 4` and the same width
`w = 2` but different means, so the width does not determine the clock.

The Lah polynomial (D1) is the corpus `lahPolynomial ℤ m` of
`Descent.Pangenome.GraphCoalescent.LahWeights`, `A_m(z) = ∑_j L(m, j) z^j`, whose coefficients
that module ties to the note's closed form `(m!/j!) C(m-1, j-1)` (`lahNumber_mul_factorial`).
The connectivity cumulant (D2) is the corpus `cumulantOfSizes T c` of
`Descent.Pangenome.GraphCoalescent.ConnectivityCumulant`, the Möbius sum over the finite
partitions of the fiber set `T`.  For two and three fibers those partitions are listed by kernel
evaluation (`sum_finpartition_fin_two`, `sum_finpartition_fin_three`), which turns (D2) into
`A_{c₀+c₁} - A_{c₀} A_{c₁}` and into the three-fiber sum with Möbius coefficients `1`, `-1` and
`2` (`cumulantOfSizes_fin_two`, `cumulantOfSizes_fin_three`).

`rankedWeight n k` is `a_{n,k}` of (D4), `connectedByLevel` is `F_k` of (D5), `firstConnectionLaw`
is `p_b` of (D6), and `meanConnectionTime` is (D8), `E τ_q = 2 ∑_b p_b / b - 2/n`.  These four
are local transcriptions of the note's formulas: the corpus module of (D4)-(D6),
`RankedHistoryLaw`, was not yet proof-checked when this file was written.  When it is, they are to
be replaced by its definitions and the rows restated against them; the arithmetic below does not
change.

Scope.  Nothing here proves (D4)-(D8), the ranked-history law and the first-connection law; those
are the business of `RankedHistoryLaw` and `ReportedConnectionClock`.  This file evaluates the
formulas at the tabulated fiber sizes.

## Empirical status

None.  The bodies here are finite enumerations and rational arithmetic on explicit polynomials,
so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.ConnectivityClockTable

open Finset Polynomial

noncomputable section

/-! ## The partitions of two and three fibers -/

/-- A sum over the finite partitions of `T` is a sum over the sets of parts they can have. -/
theorem sum_finpartition_eq_sum_parts {ι M : Type*} [DecidableEq ι] [AddCommMonoid M]
    (T : Finset ι) (F : Finset (Finset ι) → M) :
    ∑ ρ : Finpartition T, F ρ.parts =
      ∑ ps ∈ T.powerset.powerset.filter (fun ps ↦ ps.sup id = T ∧ ⊥ ∉ ps ∧ ps.SupIndep id),
        F ps := by
  refine sum_bij' (fun ρ _ ↦ ρ.parts)
    (fun ps hps ↦ ⟨ps, (mem_filter.1 hps).2.2.2, (mem_filter.1 hps).2.1,
      (mem_filter.1 hps).2.2.1⟩)
    (fun ρ _ ↦ ?_) (fun _ _ ↦ mem_univ _) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
  exact mem_filter.2 ⟨mem_powerset.2 fun p hp ↦ mem_powerset.2 (ρ.le hp), ρ.sup_parts,
    ρ.bot_notMem, ρ.supIndep⟩

/-- The finite partitions of two fibers: the one-block partition and the two singletons. -/
theorem sum_finpartition_fin_two {M : Type*} [AddCommMonoid M]
    (F : Finset (Finset (Fin 2)) → M) :
    ∑ ρ : Finpartition (univ : Finset (Fin 2)), F ρ.parts = F {univ} + F {{0}, {1}} := by
  have hparts : (univ : Finset (Fin 2)).powerset.powerset.filter
      (fun ps ↦ ps.sup id = univ ∧ ⊥ ∉ ps ∧ ps.SupIndep id) = {{univ}, {{0}, {1}}} := by
    decide +kernel
  rw [sum_finpartition_eq_sum_parts univ F, hparts]
  exact sum_pair (by decide)

/-- The finite partitions of three fibers: the one-block partition, the three partitions into a
pair and a singleton, and the three singletons. -/
theorem sum_finpartition_fin_three {M : Type*} [AddCommMonoid M]
    (F : Finset (Finset (Fin 3)) → M) :
    ∑ ρ : Finpartition (univ : Finset (Fin 3)), F ρ.parts =
      F {univ} + (F {{0, 1}, {2}} + F {{0, 2}, {1}} + F {{1, 2}, {0}}) + F {{0}, {1}, {2}} := by
  have hparts : (univ : Finset (Fin 3)).powerset.powerset.filter
      (fun ps ↦ ps.sup id = univ ∧ ⊥ ∉ ps ∧ ps.SupIndep id) =
        {{univ}, {{0, 1}, {2}}, {{0, 2}, {1}}, {{1, 2}, {0}}, {{0}, {1}, {2}}} := by
    decide +kernel
  rw [sum_finpartition_eq_sum_parts univ F, hparts]
  simp (disch := decide) only [sum_insert, sum_singleton]
  abel

/-- The Möbius coefficient of a two-block partition. -/
theorem mobiusCoefficient_two : mobiusCoefficient 2 = -1 := by
  norm_num [mobiusCoefficient]

/-- The Möbius coefficient of a three-block partition. -/
theorem mobiusCoefficient_three : mobiusCoefficient 3 = 2 := by
  norm_num [mobiusCoefficient, Nat.factorial]

/-- **(D2) for two fibers**: `C_c(z) = A_{c₀+c₁}(z) - A_{c₀}(z) A_{c₁}(z)`. -/
theorem cumulantOfSizes_fin_two (c : Fin 2 → ℕ) :
    cumulantOfSizes (univ : Finset (Fin 2)) c =
      lahPolynomial ℤ (c 0 + c 1) - lahPolynomial ℤ (c 0) * lahPolynomial ℤ (c 1) := by
  refine (sum_finpartition_fin_two
    (fun ps ↦ C (mobiusCoefficient #ps) * ∏ U ∈ ps, lahPolynomial ℤ (∑ i ∈ U, c i))).trans ?_
  simp (disch := decide) only [card_singleton, card_insert_of_notMem, prod_singleton,
    prod_insert, sum_singleton, Fin.sum_univ_two, mobiusCoefficient_one, mobiusCoefficient_two,
    _root_.map_one, _root_.map_neg, one_mul, neg_one_mul]
  ring

/-- **(D2) for three fibers**: the one-block partition with Möbius coefficient `1`, the three
partitions into a pair and a singleton with `-1` each, and the three singletons with `2`. -/
theorem cumulantOfSizes_fin_three (c : Fin 3 → ℕ) :
    cumulantOfSizes (univ : Finset (Fin 3)) c =
      lahPolynomial ℤ (c 0 + c 1 + c 2) -
        (lahPolynomial ℤ (c 0 + c 1) * lahPolynomial ℤ (c 2) +
          lahPolynomial ℤ (c 0 + c 2) * lahPolynomial ℤ (c 1) +
          lahPolynomial ℤ (c 1 + c 2) * lahPolynomial ℤ (c 0)) +
        2 * (lahPolynomial ℤ (c 0) * lahPolynomial ℤ (c 1) * lahPolynomial ℤ (c 2)) := by
  refine (sum_finpartition_fin_three
    (fun ps ↦ C (mobiusCoefficient #ps) * ∏ U ∈ ps, lahPolynomial ℤ (∑ i ∈ U, c i))).trans ?_
  simp (disch := decide) only [card_singleton, card_insert_of_notMem, prod_singleton,
    prod_insert, sum_singleton, sum_insert, Fin.sum_univ_three, mobiusCoefficient_one,
    mobiusCoefficient_two, mobiusCoefficient_three, _root_.map_one, _root_.map_neg, map_ofNat,
    one_mul, neg_one_mul]
  ring

/-! ## The formulas of (D4)-(D6) and (D8) -/

/-- The ranked-history weight `a_{n,k} = (n-k)! k! (k-1)! / (n! (n-1)!)` of (D4). -/
def rankedWeight (n k : ℕ) : ℚ :=
  ((n - k).factorial * k.factorial * (k - 1).factorial : ℚ) /
    ((n.factorial : ℚ) * ((n - 1).factorial : ℚ))

/-- The probability `F_k = a_{n,k} [z^k] C_c(z)` of (D5) that the report is connected by the time
the genealogy reaches `k` blocks. -/
def connectedByLevel (cumulant : ℤ[X]) (n k : ℕ) : ℚ :=
  rankedWeight n k * (cumulant.coeff k : ℚ)

/-- The law `p_b = F_b - F_{b+1}` of (D6) of the number of true lineages right after the first
reported connection. -/
def firstConnectionLaw (cumulant : ℤ[X]) (n b : ℕ) : ℚ :=
  connectedByLevel cumulant n b - connectedByLevel cumulant n (b + 1)

/-- The mean reported connection time (D8), `E τ_q = 2 ∑_{b=1}^{n-w+1} p_b / b - 2/n`. -/
def meanConnectionTime (cumulant : ℤ[X]) (n w : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range (n - w + 1), firstConnectionLaw cumulant n (i + 1) / ((i : ℚ) + 1) -
    2 / (n : ℚ)

/-! ## The Lah polynomials the table needs -/

/-- `A_1(z) = z`. -/
theorem lahPolynomial_one : lahPolynomial ℤ 1 = X := by
  norm_num [lahPolynomial, Finset.sum_range_succ, lahNumber]

/-- `A_2(z) = 2z + z^2`. -/
theorem lahPolynomial_two : lahPolynomial ℤ 2 = 2 * X + X ^ 2 := by
  norm_num [lahPolynomial, Finset.sum_range_succ, lahNumber, map_ofNat]

/-- `A_3(z) = 6z + 6z^2 + z^3`. -/
theorem lahPolynomial_three : lahPolynomial ℤ 3 = 6 * X + 6 * X ^ 2 + X ^ 3 := by
  norm_num [lahPolynomial, Finset.sum_range_succ, lahNumber, map_ofNat]

/-- `A_4(z) = 24z + 36z^2 + 12z^3 + z^4`. -/
theorem lahPolynomial_four : lahPolynomial ℤ 4 = 24 * X + 36 * X ^ 2 + 12 * X ^ 3 + X ^ 4 := by
  norm_num [lahPolynomial, Finset.sum_range_succ, lahNumber, map_ofNat]

/-- `A_6(z) = 720z + 1800z^2 + 1200z^3 + 300z^4 + 30z^5 + z^6`. -/
theorem lahPolynomial_six : lahPolynomial ℤ 6 =
    720 * X + 1800 * X ^ 2 + 1200 * X ^ 3 + 300 * X ^ 4 + 30 * X ^ 5 + X ^ 6 := by
  norm_num [lahPolynomial, Finset.sum_range_succ, lahNumber, map_ofNat]

/-! ## The connectivity cumulants of the table -/

/-- `C_{(1,2)}(z) = 6z + 4z^2`. -/
theorem connectivityCumulant_one_two :
    cumulantOfSizes (univ : Finset (Fin 2)) ![1, 2] = 6 * X + 4 * X ^ 2 := by
  rw [cumulantOfSizes_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, lahPolynomial_one,
    lahPolynomial_two, lahPolynomial_three]
  ring

/-- `C_{(1,3)}(z) = 24z + 30z^2 + 6z^3`. -/
theorem connectivityCumulant_one_three :
    cumulantOfSizes (univ : Finset (Fin 2)) ![1, 3] = 24 * X + 30 * X ^ 2 + 6 * X ^ 3 := by
  rw [cumulantOfSizes_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, lahPolynomial_one,
    lahPolynomial_three, lahPolynomial_four]
  ring

/-- `C_{(2,2)}(z) = 24z + 32z^2 + 8z^3`. -/
theorem connectivityCumulant_two_two :
    cumulantOfSizes (univ : Finset (Fin 2)) ![2, 2] = 24 * X + 32 * X ^ 2 + 8 * X ^ 3 := by
  rw [cumulantOfSizes_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, lahPolynomial_two,
    lahPolynomial_four]
  ring

/-- `C_{(1,1,2)}(z) = 24z + 20z^2`. -/
theorem connectivityCumulant_one_one_two :
    cumulantOfSizes (univ : Finset (Fin 3)) ![1, 1, 2] = 24 * X + 20 * X ^ 2 := by
  rw [cumulantOfSizes_fin_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, lahPolynomial_one, lahPolynomial_two, lahPolynomial_three,
    lahPolynomial_four]
  ring

/-- `C_{(2,2,2)}(z) = 720z + 1656z^2 + 928z^3 + 144z^4`. -/
theorem connectivityCumulant_two_two_two :
    cumulantOfSizes (univ : Finset (Fin 3)) ![2, 2, 2] =
      720 * X + 1656 * X ^ 2 + 928 * X ^ 3 + 144 * X ^ 4 := by
  rw [cumulantOfSizes_fin_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, lahPolynomial_two, lahPolynomial_four, lahPolynomial_six]
  ring

/-! ## The mean reported connection times of the table -/

/-- For fibers of sizes `(1,2)`, `E τ_q = 2/3`. -/
theorem meanConnectionTime_one_two :
    meanConnectionTime (cumulantOfSizes (univ : Finset (Fin 2)) ![1, 2]) 3 2 = 2 / 3 := by
  rw [connectivityCumulant_one_two]
  norm_num [meanConnectionTime, firstConnectionLaw, connectedByLevel, rankedWeight,
    Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_X_pow, Nat.factorial]

/-- For fibers of sizes `(1,3)`, `E τ_q = 1/2`. -/
theorem meanConnectionTime_one_three :
    meanConnectionTime (cumulantOfSizes (univ : Finset (Fin 2)) ![1, 3]) 4 2 = 1 / 2 := by
  rw [connectivityCumulant_one_three]
  norm_num [meanConnectionTime, firstConnectionLaw, connectedByLevel, rankedWeight,
    Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_X_pow, Nat.factorial]

/-- For fibers of sizes `(2,2)`, `E τ_q = 7/18`. -/
theorem meanConnectionTime_two_two :
    meanConnectionTime (cumulantOfSizes (univ : Finset (Fin 2)) ![2, 2]) 4 2 = 7 / 18 := by
  rw [connectivityCumulant_two_two]
  norm_num [meanConnectionTime, firstConnectionLaw, connectedByLevel, rankedWeight,
    Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_X_pow, Nat.factorial]

/-- For fibers of sizes `(1,1,2)`, `E τ_q = 17/18`. -/
theorem meanConnectionTime_one_one_two :
    meanConnectionTime (cumulantOfSizes (univ : Finset (Fin 3)) ![1, 1, 2]) 4 3 = 17 / 18 := by
  rw [connectivityCumulant_one_one_two]
  norm_num [meanConnectionTime, firstConnectionLaw, connectedByLevel, rankedWeight,
    Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_X_pow, Nat.factorial]

/-- For fibers of sizes `(2,2,2)`, `E τ_q = 92/225`. -/
theorem meanConnectionTime_two_two_two :
    meanConnectionTime (cumulantOfSizes (univ : Finset (Fin 3)) ![2, 2, 2]) 6 3 = 92 / 225 := by
  rw [connectivityCumulant_two_two_two]
  norm_num [meanConnectionTime, firstConnectionLaw, connectedByLevel, rankedWeight,
    Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_X_pow, Nat.factorial]

/-- **The width does not determine the clock.**  The fiber sizes `(1,3)` and `(2,2)` give the same
sample size `n = 4` and the same width `w = 2`, but their mean reported connection times are `1/2`
and `7/18`. -/
theorem meanConnectionTime_one_three_ne_two_two :
    1 + 3 = 2 + 2 ∧
      meanConnectionTime (cumulantOfSizes (univ : Finset (Fin 2)) ![1, 3]) 4 2 ≠
        meanConnectionTime (cumulantOfSizes (univ : Finset (Fin 2)) ![2, 2]) 4 2 := by
  refine ⟨rfl, ?_⟩
  rw [meanConnectionTime_one_three, meanConnectionTime_two_two]
  norm_num

end

end Descent.Pangenome.GraphCoalescent.ConnectivityClockTable
