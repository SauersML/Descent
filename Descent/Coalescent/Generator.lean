/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.StateSpace
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# The generator, and the contraction estimate that turns `Pₙ` into `exp(tQ)`

Kingman (1982), *On the genealogy of large populations* (**K-G**), section 2, gets the
`n`-coalescent as a limit of Wright-Fisher generations in three steps:

  `P_N = I + N⁻¹ Q + O(N⁻²)`                                                    K-G (2.11)
  `‖A₁A₂⋯A_r - B₁B₂⋯B_r‖ ≤ Σ_s ‖A_s - B_s‖` for contractions                   K-G (2.13)
  `lim_N P_N^{[Nt]} = exp(tQ)`                                                  K-G (2.14)

The first is counted in `Descent.Coalescent.WrightFisher` (`coalescenceProb_le` and
`le_coalescenceProb` bound the off-diagonal entries within `(d_k/N)²/2` of `q_{ξη}/N`).  The
second is the piece of functional analysis that carries the argument, and it is proved here
in the generality Kingman states it: any two sequences of contractions in a normed ring.
The third is the two combined, and what `pow_sub_pow_le` records is exactly the bound K-G
uses -- `[Nt] ‖P_N - exp(N⁻¹Q)‖ = O(N⁻¹)` -- with no appeal to the specific matrices.

The generator's defining property, that its rows sum to zero, is not a new theorem here: it
is `Descent.Coalescent.StateSpace.card_covers_eq_deathRate` read the other way round.  A
state with `k` blocks has `C(k,2)` covers at unit rate and diagonal entry `-d_k`, and those
cancel exactly.  `generator_row_sum_zero` says so.

## Main results

- `generator_row_sum_zero`: K-G (2.10) is a `Q`-matrix -- the off-diagonal unit rates on
  covers cancel the diagonal `-d_k` exactly.
- `norm_prodUpTo_le_one`: a product of contractions is a contraction.
- `norm_prodUpTo_sub_le`: **K-G (2.13)**.
- `pow_sub_pow_le`: its corollary for a single pair, `‖A^r - B^r‖ ≤ r ‖A - B‖`, which is the
  form K-G (2.14) uses.
-/

namespace Coalescent

open Finset

/-! ### The generator is a `Q`-matrix -/

/-- **K-G (2.10) has zero row sums.**  The diagonal entry of the coalescent generator at a
`k`-block state is `-d_k`; the off-diagonal entries are `1` on each of its covers and `0`
elsewhere.  They cancel, and the cancellation is `card_covers`: the number of covers IS
`d_k`.  A generator whose rows sum to zero is what makes `exp(tQ)` stochastic, which is the
step K-G needs to run the contraction argument at all. -/
theorem generator_row_sum_zero {n : ℕ} (ξ : ER n) :
    (Nat.card {η : ER n // Covers ξ η} : ℝ) + (-deathRate (blocks ξ)) = 0 := by
  rw [card_covers_eq_deathRate]
  ring

/-! ### The contraction estimate

K-G (2.13) is stated for stochastic matrices under the operator norm, but the proof uses
only that they are contractions in a normed ring.  It is proved in that generality here, so
nothing about the coalescent is assumed. -/

/-- The ordered product `A₀ A₁ ⋯ A_{r-1}`.  Written by recursion because the factors do not
commute, so a `Finset` product would be the wrong object. -/
def prodUpTo {M : Type*} [Monoid M] (A : ℕ → M) : ℕ → M
  | 0 => 1
  | r + 1 => prodUpTo A r * A r

@[simp] theorem prodUpTo_zero {M : Type*} [Monoid M] (A : ℕ → M) : prodUpTo A 0 = 1 := rfl

theorem prodUpTo_succ {M : Type*} [Monoid M] (A : ℕ → M) (r : ℕ) :
    prodUpTo A (r + 1) = prodUpTo A r * A r := rfl

/-- A product of contractions is a contraction. -/
theorem norm_prodUpTo_le_one {M : Type*} [NormedRing M] [NormOneClass M] (A : ℕ → M)
    (hA : ∀ s, ‖A s‖ ≤ 1) (r : ℕ) : ‖prodUpTo A r‖ ≤ 1 := by
  induction r with
  | zero => simp
  | succ m ih =>
      rw [prodUpTo_succ]
      calc ‖prodUpTo A m * A m‖ ≤ ‖prodUpTo A m‖ * ‖A m‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := by
            apply mul_le_mul ih (hA m) (norm_nonneg _) zero_le_one
        _ = 1 := by ring

/-- **K-G (2.13).**  Two products of contractions differ by at most the sum of the factorwise
differences.  Kingman calls it "well known, and easily proved by induction on `r`"; it is,
and the induction is the telescoping `A₀⋯A_r - B₀⋯B_r = (A₀⋯A_{r-1})(A_r - B_r) +
(A₀⋯A_{r-1} - B₀⋯B_{r-1})B_r`. -/
theorem norm_prodUpTo_sub_le {M : Type*} [NormedRing M] [NormOneClass M] (A B : ℕ → M)
    (hA : ∀ s, ‖A s‖ ≤ 1) (hB : ∀ s, ‖B s‖ ≤ 1) (r : ℕ) :
    ‖prodUpTo A r - prodUpTo B r‖ ≤ ∑ s ∈ range r, ‖A s - B s‖ := by
  induction r with
  | zero => simp
  | succ m ih =>
      have hsplit : prodUpTo A (m + 1) - prodUpTo B (m + 1)
          = prodUpTo A m * (A m - B m) + (prodUpTo A m - prodUpTo B m) * B m := by
        rw [prodUpTo_succ, prodUpTo_succ]
        noncomm_ring
      have h1 : ‖prodUpTo A m * (A m - B m)‖ ≤ ‖A m - B m‖ := by
        calc ‖prodUpTo A m * (A m - B m)‖ ≤ ‖prodUpTo A m‖ * ‖A m - B m‖ := norm_mul_le _ _
          _ ≤ 1 * ‖A m - B m‖ := by
              apply mul_le_mul_of_nonneg_right (norm_prodUpTo_le_one A hA m) (norm_nonneg _)
          _ = ‖A m - B m‖ := by ring
      have h2 : ‖(prodUpTo A m - prodUpTo B m) * B m‖ ≤ ∑ s ∈ range m, ‖A s - B s‖ := by
        calc ‖(prodUpTo A m - prodUpTo B m) * B m‖
            ≤ ‖prodUpTo A m - prodUpTo B m‖ * ‖B m‖ := norm_mul_le _ _
          _ ≤ ‖prodUpTo A m - prodUpTo B m‖ * 1 := by
              apply mul_le_mul_of_nonneg_left (hB m) (norm_nonneg _)
          _ = ‖prodUpTo A m - prodUpTo B m‖ := by ring
          _ ≤ ∑ s ∈ range m, ‖A s - B s‖ := ih
      rw [sum_range_succ, hsplit]
      calc ‖prodUpTo A m * (A m - B m) + (prodUpTo A m - prodUpTo B m) * B m‖
          ≤ ‖prodUpTo A m * (A m - B m)‖ + ‖(prodUpTo A m - prodUpTo B m) * B m‖ :=
            norm_add_le _ _
        _ ≤ ‖A m - B m‖ + ∑ s ∈ range m, ‖A s - B s‖ := by
            exact add_le_add h1 h2
        _ = ∑ s ∈ range m, ‖A s - B s‖ + ‖A m - B m‖ := by ring

/-- Constant sequences are the case K-G (2.14) uses: `‖P_N^{[Nt]} - exp(N⁻¹Q)^{[Nt]}‖ ≤
[Nt] ‖P_N - exp(N⁻¹Q)‖`, which is `O(N⁻¹)` once the one-step difference is `O(N⁻²)`.  That
is the whole convergence argument, minus the entrywise expansion that
`Descent.Coalescent.WrightFisher` supplies. -/
theorem pow_sub_pow_le {M : Type*} [NormedRing M] [NormOneClass M] (A B : M)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (r : ℕ) :
    ‖prodUpTo (fun _ ↦ A) r - prodUpTo (fun _ ↦ B) r‖ ≤ (r : ℝ) * ‖A - B‖ := by
  have h := norm_prodUpTo_sub_le (fun _ ↦ A) (fun _ ↦ B) (fun _ ↦ hA) (fun _ ↦ hB) r
  simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h

/-- The ordered product of a constant sequence is the power, so `pow_sub_pow_le` really is
about `A^r`. -/
theorem prodUpTo_const {M : Type*} [Monoid M] (A : M) (r : ℕ) :
    prodUpTo (fun _ ↦ A) r = A ^ r := by
  induction r with
  | zero => simp
  | succ m ih =>
      rw [prodUpTo_succ, ih, pow_succ]

end Coalescent

end Descent
