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


/-! ## The equal-weight reports as functions of the aligned-locus count -/

/-- The conditional squared correlation of an equal-weight architecture with `k` aligned
loci out of `n`, DC (4.2). -/
def countR2 (n : ℕ) (ν : ℝ) (k : ℕ) : ℝ := ((2 * (k : ℝ) - (n : ℝ)) / (n : ℝ)) ^ 2 / (1 + ν)

/-- The conditional mean squared error of an equal-weight architecture with `k` aligned
loci out of `n`, DC (4.2). -/
def countMse (n : ℕ) (ν : ℝ) (k : ℕ) : ℝ := ν + 2 * (1 - (2 * (k : ℝ) - (n : ℝ)) / (n : ℝ))

/-- The count report is the population's own `r2`. -/
theorem countR2_eq_architecture_r2 {n : ℕ} {V : Type*} [Fintype V] (noise : ExpFunctional V)
    (σ : Fin n → Bool) (ξ : V → ℝ) (hn : 0 < n) (hmean : noise ξ = 0) :
    countR2 n (noise (fun e ↦ ξ e ^ 2)) (ConvexOrderCoupling.occupiedCount σ)
      = (architecturePop n noise (equalWeights n) σ ξ).r2 (equalWeights n) := by
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hc : (1 + noise (fun e ↦ ξ e ^ 2)) ≠ 0 := by
    have := noise_var_nonneg noise ξ
    intro hcon
    linarith
  rw [equal_weight_r2 noise σ ξ hn hmean, sum_signValue_eq]
  simp only [countR2]
  field_simp

/-- The count report is the population's own `deployedMse`. -/
theorem countMse_eq_architecture_mse {n : ℕ} {V : Type*} [Fintype V]
    (noise : ExpFunctional V) (σ : Fin n → Bool) (ξ : V → ℝ) (hn : 0 < n)
    (hmean : noise ξ = 0) :
    countMse n (noise (fun e ↦ ξ e ^ 2)) (ConvexOrderCoupling.occupiedCount σ)
      = (architecturePop n noise (equalWeights n) σ ξ).deployedMse (equalWeights n) := by
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [equal_weight_mse noise σ ξ hn hmean]
  simp only [countMse, reversedCount]
  field_simp
  ring

/-- At full alignment the squared correlation is `1/(1+ν)`. -/
theorem countR2_top (n : ℕ) (ν : ℝ) (hn : 0 < n) : countR2 n ν n = 1 / (1 + ν) := by
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h : (2 * (n : ℝ) - (n : ℝ)) / (n : ℝ) = 1 := by
    field_simp
    norm_num
  simp only [countR2]
  rw [h]
  norm_num

/-- At full reversal the squared correlation is also `1/(1+ν)`: a coherent sign reversal
preserves squared correlation.  DC §4.2 records this as the reason both metrics matter. -/
theorem countR2_bot (n : ℕ) (ν : ℝ) (hn : 0 < n) : countR2 n ν 0 = 1 / (1 + ν) := by
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h : (2 * ((0 : ℕ) : ℝ) - (n : ℝ)) / (n : ℝ) = -1 := by
    rw [Nat.cast_zero]
    field_simp
    ring
  simp only [countR2]
  rw [h]
  norm_num

/-- At full alignment the mean squared error is the noise variance. -/
theorem countMse_top (n : ℕ) (ν : ℝ) (hn : 0 < n) : countMse n ν n = ν := by
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h : (2 * (n : ℝ) - (n : ℝ)) / (n : ℝ) = 1 := by
    field_simp
    norm_num
  simp only [countMse]
  rw [h]
  ring

/-- At full reversal the mean squared error is `ν + 4`: the same squared correlation, a
very different raw prediction error. -/
theorem countMse_bot (n : ℕ) (ν : ℝ) (hn : 0 < n) : countMse n ν 0 = ν + 4 := by
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h : (2 * ((0 : ℕ) : ℝ) - (n : ℝ)) / (n : ℝ) = -1 := by
    rw [Nat.cast_zero]
    field_simp
    ring
  simp only [countMse]
  rw [h]
  ring

/-! ## The two extremal aggregate laws and the sharp interval -/

/-- The synchronous coupling's aggregate law: every locus is aligned with probability
`(1+p)/2`, every locus is reversed with probability `(1-p)/2`.  Each coordinate then has
mean sign `p`, the same one-locus law as the binomial coupling. -/
def syncExp (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ExpFunctional (Fin 2) :=
  weightedExp ![(1 - p) / 2, (1 + p) / 2]
    (by
      intro i
      fin_cases i
      · show (0 : ℝ) ≤ (1 - p) / 2
        linarith
      · show (0 : ℝ) ≤ (1 + p) / 2
        linarith)
    (by
      rw [Fin.sum_univ_two]
      show (1 - p) / 2 + (1 + p) / 2 = 1
      ring)

/-- The synchronous coupling's aligned-locus count: all or nothing. -/
def syncCount (n : ℕ) : Fin 2 → ℕ := ![0, n]

/-- **DC Corollary 3.5 / Theorem 4.2, lower endpoint; PL Corollary 5.4.**  With `n = 2m`
even and the minimizing aggregate law `N = m + Binomial(m, p)`, the mean conditional
squared correlation is exactly `((1 - 2/n)p² + (2/n)p)/(1+ν)`. -/
theorem binomial_envelope_lower (m : ℕ) (hm : 0 < m) (p ν : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hν : 0 ≤ ν) :
    binomialExp m p hp0 hp1 (fun k ↦ countR2 (2 * m) ν (m + (k : ℕ)))
      = ((1 - 2 / (2 * (m : ℝ))) * p ^ 2 + (2 / (2 * (m : ℝ))) * p) / (1 + ν) := by
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hc : (1 + ν) ≠ 0 := by
    intro hcon
    linarith
  have hfun : ∀ k : ℕ,
      countR2 (2 * m) ν (m + k) = (1 / ((m : ℝ) ^ 2 * (1 + ν))) * ((k : ℝ) ^ 2) := by
    intro k
    simp only [countR2]
    push_cast
    field_simp
    ring
  have hfun2 : (fun k : Fin (m + 1) ↦ countR2 (2 * m) ν (m + (k : ℕ)))
      = (fun k : Fin (m + 1) ↦ (1 / ((m : ℝ) ^ 2 * (1 + ν))) * ((((k : ℕ)) : ℝ) ^ 2)) :=
    funext fun k ↦ hfun (k : ℕ)
  rw [hfun2, binomialExp_eq_binMoment m p hp0 hp1
    (fun j : ℕ ↦ (1 / ((m : ℝ) ^ 2 * (1 + ν))) * ((j : ℝ) ^ 2)),
    binMoment_smul, binMoment_sq]
  field_simp
  ring

/-- **DC Theorem 4.2, upper endpoint.**  The synchronous coupling reports `1/(1+ν)` at
every time: its aggregate squared correlation is one whichever way the block points. -/
theorem sync_envelope_upper (m : ℕ) (hm : 0 < m) (p ν : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    syncExp p hp0 hp1 (fun i ↦ countR2 (2 * m) ν (syncCount (2 * m) i)) = 1 / (1 + ν) := by
  have hn : 0 < 2 * m := by omega
  have h0 : countR2 (2 * m) ν (syncCount (2 * m) 0) = 1 / (1 + ν) := countR2_bot _ _ hn
  have h1 : countR2 (2 * m) ν (syncCount (2 * m) 1) = 1 / (1 + ν) := countR2_top _ _ hn
  show ∑ i : Fin 2, ![(1 - p) / 2, (1 + p) / 2] i
      * countR2 (2 * m) ν (syncCount (2 * m) i) = 1 / (1 + ν)
  rw [Fin.sum_univ_two, h0, h1]
  show (1 - p) / 2 * (1 / (1 + ν)) + (1 + p) / 2 * (1 / (1 + ν)) = 1 / (1 + ν)
  ring

/-- **DC (4.5), first half.**  The minimizing coupling's mean squared error is
`ν + 2(1 - p)`. -/
theorem binomial_envelope_mse (m : ℕ) (hm : 0 < m) (p ν : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binomialExp m p hp0 hp1 (fun k ↦ countMse (2 * m) ν (m + (k : ℕ)))
      = ν + 2 * (1 - p) := by
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hfun : ∀ k : ℕ,
      countMse (2 * m) ν (m + k) = (ν + 2) * 1 + (-(2 / (m : ℝ))) * ((k : ℝ)) := by
    intro k
    simp only [countMse]
    push_cast
    field_simp
    ring
  have hfun2 : (fun k : Fin (m + 1) ↦ countMse (2 * m) ν (m + (k : ℕ)))
      = (fun k : Fin (m + 1) ↦ (ν + 2) * 1 + (-(2 / (m : ℝ))) * ((((k : ℕ)) : ℝ))) :=
    funext fun k ↦ hfun (k : ℕ)
  rw [hfun2, binomialExp_eq_binMoment m p hp0 hp1
    (fun j : ℕ ↦ (ν + 2) * 1 + (-(2 / (m : ℝ))) * ((j : ℝ))),
    binMoment_add p (fun j : ℕ ↦ (ν + 2) * 1) (fun j : ℕ ↦ (-(2 / (m : ℝ))) * ((j : ℝ))) m,
    binMoment_smul p (ν + 2) (fun _ ↦ (1 : ℝ)) m,
    binMoment_smul p (-(2 / (m : ℝ))) (fun j : ℕ ↦ ((j : ℝ))) m, binMoment_one, binMoment_id]
  field_simp
  ring

/-- **DC (4.5), second half.**  The synchronous coupling's mean squared error is the same
`ν + 2(1 - p)`: the mean squared error is invariant across the whole envelope. -/
theorem sync_envelope_mse (m : ℕ) (hm : 0 < m) (p ν : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    syncExp p hp0 hp1 (fun i ↦ countMse (2 * m) ν (syncCount (2 * m) i)) = ν + 2 * (1 - p) := by
  have hn : 0 < 2 * m := by omega
  have h0 : countMse (2 * m) ν (syncCount (2 * m) 0) = ν + 4 := countMse_bot _ _ hn
  have h1 : countMse (2 * m) ν (syncCount (2 * m) 1) = ν := countMse_top _ _ hn
  show ∑ i : Fin 2, ![(1 - p) / 2, (1 + p) / 2] i
      * countMse (2 * m) ν (syncCount (2 * m) i) = ν + 2 * (1 - p)
  rw [Fin.sum_univ_two, h0, h1]
  show (1 - p) / 2 * (ν + 4) + (1 + p) / 2 * ν = ν + 2 * (1 - p)
  ring

/-! ## Every intermediate value is attained -/

/-- A time-zero randomization between two couplings.  DC Theorem 4.2 uses exactly this:
an independent time-zero choice preserves every conditional coordinate rate, so the mixture
is admissible and reports the convex combination. -/
def mixTwo {Ω1 Ω2 : Type*} (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (E1 : ExpFunctional Ω1) (E2 : ExpFunctional Ω2) : ExpFunctional (Ω1 ⊕ Ω2) where
  eval f := θ * E1 (fun x ↦ f (Sum.inl x)) + (1 - θ) * E2 (fun y ↦ f (Sum.inr y))
  add_eval f g := by
    show θ * E1 ((fun x ↦ f (Sum.inl x)) + fun x ↦ g (Sum.inl x))
        + (1 - θ) * E2 ((fun y ↦ f (Sum.inr y)) + fun y ↦ g (Sum.inr y)) = _
    rw [E1.add_eval, E2.add_eval]
    ring
  smul_eval c f := by
    show θ * E1 (c • fun x ↦ f (Sum.inl x)) + (1 - θ) * E2 (c • fun y ↦ f (Sum.inr y)) = _
    rw [E1.smul_eval, E2.smul_eval]
    ring
  const_one := by
    show θ * E1 (fun _ ↦ (1 : ℝ)) + (1 - θ) * E2 (fun _ ↦ (1 : ℝ)) = 1
    rw [E1.const_one, E2.const_one]
    ring
  nonneg_eval f hf :=
    add_nonneg (mul_nonneg hθ0 (E1.nonneg_eval _ fun x ↦ hf _))
      (mul_nonneg (by linarith) (E2.nonneg_eval _ fun y ↦ hf _))

/-- Evaluation of a time-zero randomization. -/
theorem mixTwo_apply {Ω1 Ω2 : Type*} (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (E1 : ExpFunctional Ω1) (E2 : ExpFunctional Ω2) (f : Ω1 ⊕ Ω2 → ℝ) :
    mixTwo θ hθ0 hθ1 E1 E2 f
      = θ * E1 (fun x ↦ f (Sum.inl x)) + (1 - θ) * E2 (fun y ↦ f (Sum.inr y)) := rfl

/-- **DC Theorem 4.2, intermediate values.**  The randomized coupling reports the convex
combination of the two endpoints. -/
theorem envelope_mixture_r2 (m : ℕ) (hm : 0 < m) (p ν θ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hν : 0 ≤ ν) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    mixTwo θ hθ0 hθ1 (binomialExp m p hp0 hp1) (syncExp p hp0 hp1)
        (Sum.elim (fun k : Fin (m + 1) ↦ countR2 (2 * m) ν (m + (k : ℕ)))
          (fun i : Fin 2 ↦ countR2 (2 * m) ν (syncCount (2 * m) i)))
      = θ * (((1 - 2 / (2 * (m : ℝ))) * p ^ 2 + (2 / (2 * (m : ℝ))) * p) / (1 + ν))
        + (1 - θ) * (1 / (1 + ν)) := by
  rw [mixTwo_apply]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [binomial_envelope_lower m hm p ν hp0 hp1 hν, sync_envelope_upper m hm p ν hp0 hp1]

/-- **DC (4.5) across the envelope.**  Every randomized coupling reports the same mean
squared error `ν + 2(1 - p)`, whatever the squared correlation it reports. -/
theorem envelope_mixture_mse (m : ℕ) (hm : 0 < m) (p ν θ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    mixTwo θ hθ0 hθ1 (binomialExp m p hp0 hp1) (syncExp p hp0 hp1)
        (Sum.elim (fun k : Fin (m + 1) ↦ countMse (2 * m) ν (m + (k : ℕ)))
          (fun i : Fin 2 ↦ countMse (2 * m) ν (syncCount (2 * m) i)))
      = ν + 2 * (1 - p) := by
  rw [mixTwo_apply]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [binomial_envelope_mse m hm p ν hp0 hp1, sync_envelope_mse m hm p ν hp0 hp1]
  ring

/-- **Every value of the sharp interval is attained.**  Given any target between the two
endpoints, an explicit time-zero randomization weight reports exactly it. -/
theorem envelope_attains (m : ℕ) (hm : 0 < m) (p ν v : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hν : 0 ≤ ν)
    (hlow : ((1 - 2 / (2 * (m : ℝ))) * p ^ 2 + (2 / (2 * (m : ℝ))) * p) / (1 + ν) ≤ v)
    (hup : v ≤ 1 / (1 + ν))
    (hlt : ((1 - 2 / (2 * (m : ℝ))) * p ^ 2 + (2 / (2 * (m : ℝ))) * p) / (1 + ν)
      < 1 / (1 + ν)) :
    ∃ (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
      mixTwo θ h0 h1 (binomialExp m p hp0 hp1) (syncExp p hp0 hp1)
        (Sum.elim (fun k : Fin (m + 1) ↦ countR2 (2 * m) ν (m + (k : ℕ)))
          (fun i : Fin 2 ↦ countR2 (2 * m) ν (syncCount (2 * m) i))) = v := by
  set lo := ((1 - 2 / (2 * (m : ℝ))) * p ^ 2 + (2 / (2 * (m : ℝ))) * p) / (1 + ν) with hlodef
  set up := 1 / (1 + ν) with hupdef
  have hgap : 0 < up - lo := by linarith
  have hne : up - lo ≠ 0 := ne_of_gt hgap
  refine ⟨(up - v) / (up - lo), div_nonneg (by linarith) (le_of_lt hgap), ?_, ?_⟩
  · rw [div_le_one hgap]
    linarith
  · rw [envelope_mixture_r2 m hm p ν _ hp0 hp1 hν, ← hlodef, ← hupdef]
    field_simp
    ring

end

end Descent.Portability.BinomialAggregateEnvelope
