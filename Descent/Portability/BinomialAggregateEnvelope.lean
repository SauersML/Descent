/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TurnoverArchitectureMetrics

assert_below Descent.Decision Descent.Program

/-!
# The binomial aggregate law and the sharp portability interval

This module builds the two extremal aggregate laws of DC Corollary 3.5 / Theorem 4.2 and
PL Corollary 5.4 and evaluates the manuscript's reports on them exactly.

`binWeight` is the Binomial law written through its Pascal recursion, so its normalization,
mean and second moment are proved by induction rather than assumed from a binomial-
coefficient identity; `binomialExp` packages it as a corpus `ExpFunctional` through
`weightedExp`. `countR2` and `countMse` are the equal-weight conditional squared
correlation and mean squared error expressed through the aligned-locus count alone; they
are tied to `Descent.Portability.TurnoverArchitectureMetrics.architecturePop` by
`countR2_eq_architecture_r2` and `countMse_eq_architecture_mse`, so the envelope below is
an envelope for the corpus's own `r2` and `deployedMse`.

Domain conditions: `0 ≤ p ≤ 1` (a survival probability, `p = e^{-2λt}`), `0 < m` and
`n = 2m` (the even case of DC (4.4)), and a nonnegative noise variance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BinomialAggregateEnvelope

open Foundations TurnoverArchitectureMetrics

noncomputable section

/-! ## The binomial law through its Pascal recursion -/

/-- Binomial weights defined by the Pascal recursion: `w_{m+1}(k) = (1-r) w_m(k) + r
w_m(k-1)`.  No binomial-coefficient identity is used anywhere below. -/
def binWeight (r : ℝ) : ℕ → ℕ → ℝ
  | 0, k => if k = 0 then 1 else 0
  | (m + 1), k =>
      (1 - r) * binWeight r m k + r * (if k = 0 then 0 else binWeight r m (k - 1))

/-- The base case of the Pascal recursion. -/
theorem binWeight_zero (r : ℝ) (k : ℕ) : binWeight r 0 k = if k = 0 then 1 else 0 := rfl

/-- The Pascal recursion at the bottom state. -/
theorem binWeight_succ_zero (r : ℝ) (m : ℕ) :
    binWeight r (m + 1) 0 = (1 - r) * binWeight r m 0 := by
  simp [binWeight]

/-- The Pascal recursion at a positive state. -/
theorem binWeight_succ_succ (r : ℝ) (m k : ℕ) :
    binWeight r (m + 1) (k + 1) = (1 - r) * binWeight r m (k + 1) + r * binWeight r m k := by
  simp [binWeight]

/-- Binomial weights are nonnegative for a probability `r`. -/
theorem binWeight_nonneg (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (m : ℕ) :
    ∀ k : ℕ, 0 ≤ binWeight r m k := by
  induction m with
  | zero =>
    intro k
    rw [binWeight_zero]
    split <;> norm_num
  | succ m ih =>
    intro k
    cases k with
    | zero =>
      rw [binWeight_succ_zero]
      exact mul_nonneg (by linarith) (ih 0)
    | succ k =>
      rw [binWeight_succ_succ]
      exact add_nonneg (mul_nonneg (by linarith) (ih (k + 1))) (mul_nonneg hr0 (ih k))

/-- The binomial law lives on `{0, …, m}`. -/
theorem binWeight_eq_zero_of_lt (r : ℝ) (m : ℕ) : ∀ k : ℕ, m < k → binWeight r m k = 0 := by
  induction m with
  | zero =>
    intro k hk
    rw [binWeight_zero, if_neg (by omega)]
  | succ m ih =>
    intro k hk
    cases k with
    | zero => omega
    | succ k =>
      rw [binWeight_succ_succ, ih (k + 1) (by omega), ih k (by omega)]
      ring

/-- The expectation of `g` under the Binomial`(m, r)` law. -/
def binMoment (r : ℝ) (g : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), g k * binWeight r m k

/-- Equal reports have equal binomial expectations. -/
theorem binMoment_congr (r : ℝ) {g1 g2 : ℕ → ℝ} (h : ∀ k, g1 k = g2 k) (m : ℕ) :
    binMoment r g1 m = binMoment r g2 m := by
  simp only [binMoment]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [h k]

/-- Additivity of the binomial expectation. -/
theorem binMoment_add (r : ℝ) (g1 g2 : ℕ → ℝ) (m : ℕ) :
    binMoment r (fun k ↦ g1 k + g2 k) m = binMoment r g1 m + binMoment r g2 m := by
  simp only [binMoment, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- Homogeneity of the binomial expectation. -/
theorem binMoment_smul (r : ℝ) (c : ℝ) (g : ℕ → ℝ) (m : ℕ) :
    binMoment r (fun k ↦ c * g k) m = c * binMoment r g m := by
  simp only [binMoment, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- **The one-trial recursion for binomial expectations.**  Conditioning on the last trial
turns the expectation at `m + 1` into a `(1 - r, r)` combination of the expectation of the
report and of its unit shift at `m`. -/
theorem binMoment_succ (r : ℝ) (g h : ℕ → ℝ) (hgh : ∀ k, h k = g (k + 1)) (m : ℕ) :
    binMoment r g (m + 1) = (1 - r) * binMoment r g m + r * binMoment r h m := by
  have hzero : binWeight r m (m + 1) = 0 := binWeight_eq_zero_of_lt r m (m + 1) (by omega)
  have hstep : ∀ i : ℕ, g (i + 1) * binWeight r (m + 1) (i + 1)
      = (1 - r) * (g (i + 1) * binWeight r m (i + 1)) + r * (h i * binWeight r m i) := by
    intro i
    rw [binWeight_succ_succ, hgh i]
    ring
  have hzeroterm : g 0 * binWeight r (m + 1) 0 = (1 - r) * (g 0 * binWeight r m 0) := by
    rw [binWeight_succ_zero]
    ring
  have hshift : ∑ i ∈ Finset.range (m + 1), g (i + 1) * binWeight r m (i + 1)
      + g 0 * binWeight r m 0 = ∑ k ∈ Finset.range (m + 1), g k * binWeight r m k := by
    rw [← Finset.sum_range_succ' (fun k ↦ g k * binWeight r m k) (m + 1),
      Finset.sum_range_succ, hzero]
    ring
  simp only [binMoment]
  rw [Finset.sum_range_succ' (fun k ↦ g k * binWeight r (m + 1) k) (m + 1),
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.range (m + 1)) ↦ hstep i, hzeroterm,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  linear_combination (1 - r) * hshift

/-- The binomial law is a probability law. -/
theorem binMoment_one (r : ℝ) (m : ℕ) : binMoment r (fun _ ↦ (1 : ℝ)) m = 1 := by
  induction m with
  | zero => simp [binMoment, binWeight_zero]
  | succ m ih =>
    rw [binMoment_succ r (fun _ ↦ (1 : ℝ)) (fun _ ↦ (1 : ℝ)) (fun _ ↦ rfl) m, ih]
    ring

/-- **The binomial mean** `m r`, proved from the Pascal recursion. -/
theorem binMoment_id (r : ℝ) (m : ℕ) :
    binMoment r (fun k ↦ (k : ℝ)) m = (m : ℝ) * r := by
  induction m with
  | zero => simp [binMoment, binWeight_zero]
  | succ m ih =>
    have hshift : binMoment r (fun k ↦ (k : ℝ) + 1) m = (m : ℝ) * r + 1 := by
      rw [binMoment_add r (fun k ↦ (k : ℝ)) (fun _ ↦ (1 : ℝ)) m, ih, binMoment_one]
    rw [binMoment_succ r (fun k ↦ (k : ℝ)) (fun k ↦ (k : ℝ) + 1)
      (fun k ↦ by push_cast; ring) m, ih, hshift]
    push_cast
    ring

/-- **The binomial second moment** `m r (1 - r) + (m r)²`, proved from the Pascal
recursion. -/
theorem binMoment_sq (r : ℝ) (m : ℕ) :
    binMoment r (fun k ↦ (k : ℝ) ^ 2) m = (m : ℝ) * r * (1 - r) + ((m : ℝ) * r) ^ 2 := by
  induction m with
  | zero => simp [binMoment, binWeight_zero]
  | succ m ih =>
    have hexp : binMoment r (fun k ↦ ((k : ℝ) + 1) ^ 2) m
        = binMoment r (fun k ↦ (k : ℝ) ^ 2) m
          + (2 * binMoment r (fun k ↦ (k : ℝ)) m + binMoment r (fun _ ↦ (1 : ℝ)) m) := by
      rw [← binMoment_smul r 2 (fun k ↦ (k : ℝ)) m,
        ← binMoment_add r (fun k ↦ 2 * (k : ℝ)) (fun _ ↦ (1 : ℝ)) m,
        ← binMoment_add r (fun k ↦ (k : ℝ) ^ 2) (fun k ↦ 2 * (k : ℝ) + 1) m]
      exact binMoment_congr r (fun k ↦ by ring) m
    rw [binMoment_succ r (fun k ↦ (k : ℝ) ^ 2) (fun k ↦ ((k : ℝ) + 1) ^ 2)
      (fun k ↦ by push_cast; ring) m, hexp, ih, binMoment_id, binMoment_one]
    push_cast
    ring

/-! ## The binomial law as a corpus expectation functional -/

/-- The Binomial`(m, r)` law on `{0, …, m}` as an expectation functional. -/
def binomialExp (m : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : ExpFunctional (Fin (m + 1)) :=
  weightedExp (fun k ↦ binWeight r m (k : ℕ))
    (fun k ↦ binWeight_nonneg r hr0 hr1 m (k : ℕ))
    (by
      rw [Fin.sum_univ_eq_sum_range (fun j ↦ binWeight r m j) (m + 1)]
      have h := binMoment_one r m
      simp only [binMoment, one_mul] at h
      exact h)

/-- The binomial expectation functional computes binomial moments. -/
theorem binomialExp_eq_binMoment (m : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (g : ℕ → ℝ) :
    binomialExp m r hr0 hr1 (fun k ↦ g (k : ℕ)) = binMoment r g m := by
  show ∑ k : Fin (m + 1), binWeight r m (k : ℕ) * g (k : ℕ) = binMoment r g m
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ binWeight r m j * g j) (m + 1)]
  simp only [binMoment]
  exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _

end

end Descent.Portability.BinomialAggregateEnvelope
