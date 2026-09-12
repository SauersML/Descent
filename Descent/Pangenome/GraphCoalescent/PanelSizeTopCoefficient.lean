/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.PanelSizeIdentifiability
import Descent.Pangenome.GraphCoalescent.ConnectivityClockTable
import Mathlib.Algebra.Group.ForwardDiff

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The top spectral coefficient of the connection clock

`PanelSizeIdentifiability.panelSize_eq_of_survivalAt_eq` identifies the panel size `n` from the
survival function of the reported connection time whenever the top spectral coefficient
`σ_n = spectralCoeff s ⊥ n`, the coefficient of `e^{-d_n c}`, is nonzero. This file computes that
coefficient.

## The residue formula

- `spectralCoeff_bot_self_mul_eq`: clearing denominators in
  `1 - ∑_k σ_k t/(t + d_k) = ∑_b p_b ∏_{k=b+1}^{n} d_k/(d_k + t)` gives a polynomial identity in
  `t`, and at `t = -d_n` only the top coefficient survives on the left:
  `σ_n d_n ∏_{j<n} (d_j - d_n) = ∑_{b<n} p_b ∏_{k=b+1}^{n} d_k ∏_{k≤b} (d_k - d_n)`.
- `spectralCoeff_bot_self_eq`: the residue formula
  `σ_n = ∑_{b<n} p_b ∏_{k=b+1}^{n-1} d_k/(d_k - d_n)`.

## The finite-difference form

- `ladderResidue_mul_choose`: the ladder residue is a signed product of binomials,
  `C(2n-2, n-1) ∏_{k=b+1}^{n-1} d_k/(d_k - d_n) = (-1)^{n-1-b} C(n-2, b-1) C(n+b-1, n-1)`.
  The proof is a downward induction on `b`. Taking the factor `k = b + 1` off the product
  multiplies by `d_{b+1}/(d_{b+1} - d_n) = -(b+1)b/((n-1-b)(n+b))`, and two Pascal identities
  turn that into the ratio of the binomials (`ladderResidue_mul_choose_aux`).
- `spectralCoeff_bot_self_mul_choose`: so
  `σ_n C(2n-2, n-1) = ∑_{b=1}^{n-1} (-1)^{n-1-b} C(n-2, b-1) g(b)` with `g(b) = p_b C(n+b-1, n-1)`,
  and `spectralCoeff_bot_self_mul_choose_eq_fwdDiff` writes the sum as Mathlib's iterated forward
  difference `Δ^{n-2} g (1)`.

## The injective interface

- `stoppingProb_of_injective`: an injective interface connects only at the root, `B = 1` surely.
- `spectralCoeff_bot_self_of_injective`: so `σ_n = ∏_{k=2}^{n-1} d_k/(d_k - d_n)`, a product of
  nonzero factors (`spectralCoeff_bot_self_ne_zero_of_injective`).
- `spectralCoeff_bot_self_mul_choose_of_injective`: the ladder residue at `b = 1` gives
  `σ_n C(2n-2, n-1) = (-1)^n n`, that is `σ_n = (-1)^n / C_{n-1}` with `C_{n-1}` the Catalan
  number.
- `panelSize_eq_of_survivalAt_eq_of_injective`: the survival function of the clock of an
  injective interface determines `n`.

## Scope

Not formalized: the family with fibers of sizes `1` and `n - 1`. By hand, the cumulant is
`A_n - z A_{n-1}`, so `F_k = 1 - d_k/d_n` and `p_b = b/d_n`. The finite difference of
`spectralCoeff_bot_self_mul_choose_eq_fwdDiff` is then `Δ^{n-2}` of `n C(n+x, n)/d_n` at `x = 0`,
which is `n C(n, 2)/d_n = n`, so `σ_n = 1/C_{n-1}` and that family would name `n` as well.

Open: whether `(-1)^w σ_n > 0` for every interface of width `w ≥ 2`, which would make `n`
identified from the law exactly when `w ≥ 2` (width one is the collision of
`PanelSizeIdentifiability.exists_panelSize_collision`). Remark, computed by hand from the
cumulant tables and not formalized: the sign `(-1)^w` holds for every interface with `n ≤ 5` and
for `(1, 5)` and `(3, 3)` at `n = 6`, for instance `σ_4 = 7/15` for `(2, 2)`, `σ_5 = -1/2` for
`(1, 2, 2)` and `σ_6 = 101/420` for `(3, 3)`.

## Empirical status

None. The bodies are identities between the laws of the connection clock, finite sums and
binomial coefficients, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.PanelSizeTopCoefficient

open Coalescent Finset MeasureTheory fwdDiff
open scoped Classical ENNReal NNReal

/-! ### The residue formula -/

/-- **The residue formula, multiplied out.** For `n ≥ 2`,
`σ_n d_n ∏_{j=2}^{n-1} (d_j - d_n)`
`= ∑_{b=1}^{n-1} p_b ∏_{k=b+1}^{n} d_k ∏_{k=2}^{b} (d_k - d_n)`. -/
theorem spectralCoeff_bot_self_mul_eq {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    spectralCoeff s ⊥ n * (deathRate n * ∏ j ∈ Ioc 1 (n - 1), (deathRate j - deathRate n))
      = ∑ b ∈ Ico 1 n, stoppingProb s b * (∏ k ∈ Ioc b n, deathRate k)
          * ∏ k ∈ Ioc 1 b, (deathRate k - deathRate n) := by
  have hlap : ∀ t : ℝ, 0 ≤ t →
      1 - ∑ k ∈ Ioc 1 n, spectralCoeff s ⊥ k * (t / (t + deathRate k))
        = ∑ b ∈ Icc 1 n, stoppingProb s b * ∏ k ∈ Ioc b n, deathRate k / (deathRate k + t) := by
    intro t ht
    have h1 := ConnectionLawIdentifiability.connectionLaplace_eq_one_sub_sum_spectralCoeff s ht ⊥
    rw [blocks_bot] at h1
    rw [← h1]
    exact ConnectionLawIdentifiability.connectionLaplace_bot_eq_sum_stoppingProb hn s
  have hclear : ∀ t : ℝ, 0 ≤ t →
      ∏ k ∈ Ioc 1 n, (t + deathRate k)
        - ∑ k ∈ Ioc 1 n, spectralCoeff s ⊥ k * t * ∏ j ∈ (Ioc 1 n).erase k, (t + deathRate j)
      = ∑ b ∈ Icc 1 n, stoppingProb s b * (∏ k ∈ Ioc b n, deathRate k)
          * ∏ k ∈ Ioc 1 b, (t + deathRate k) := by
    intro t ht
    have hpos : ∀ k ∈ Ioc 1 n, 0 < t + deathRate k := fun k hk ↦
      add_pos_of_nonneg_of_pos ht (deathRate_pos (by have := (mem_Ioc.mp hk).1; omega))
    have hL : ∀ k ∈ Ioc 1 n,
        spectralCoeff s ⊥ k * (t / (t + deathRate k)) * ∏ j ∈ Ioc 1 n, (t + deathRate j)
          = spectralCoeff s ⊥ k * t * ∏ j ∈ (Ioc 1 n).erase k, (t + deathRate j) := by
      intro k hk
      have hc : t / (t + deathRate k) * (t + deathRate k) = t :=
        div_mul_cancel₀ t (hpos k hk).ne'
      rw [← mul_prod_erase _ _ hk]
      calc spectralCoeff s ⊥ k * (t / (t + deathRate k))
            * ((t + deathRate k) * ∏ j ∈ (Ioc 1 n).erase k, (t + deathRate j))
          = spectralCoeff s ⊥ k * (∏ j ∈ (Ioc 1 n).erase k, (t + deathRate j))
              * (t / (t + deathRate k) * (t + deathRate k)) := by ring
        _ = spectralCoeff s ⊥ k * t * ∏ j ∈ (Ioc 1 n).erase k, (t + deathRate j) := by
            rw [hc]
            ring
    have hR : ∀ b ∈ Icc 1 n,
        stoppingProb s b * (∏ k ∈ Ioc b n, deathRate k / (deathRate k + t))
            * ∏ k ∈ Ioc 1 n, (t + deathRate k)
          = stoppingProb s b * (∏ k ∈ Ioc b n, deathRate k)
            * ∏ k ∈ Ioc 1 b, (t + deathRate k) := by
      intro b hb
      obtain ⟨hb1, hbn⟩ := mem_Icc.mp hb
      have hsplit : ∏ k ∈ Ioc 1 n, (t + deathRate k)
          = (∏ k ∈ Ioc 1 b, (t + deathRate k)) * ∏ k ∈ Ioc b n, (t + deathRate k) :=
        (prod_Ioc_consecutive _ hb1 hbn).symm
      have hcancel : (∏ k ∈ Ioc b n, deathRate k / (deathRate k + t))
            * ∏ k ∈ Ioc b n, (t + deathRate k) = ∏ k ∈ Ioc b n, deathRate k := by
        rw [← prod_mul_distrib]
        refine prod_congr rfl fun k hk ↦ ?_
        have hk' : k ∈ Ioc 1 n :=
          mem_Ioc.mpr ⟨by have := (mem_Ioc.mp hk).1; omega, (mem_Ioc.mp hk).2⟩
        rw [add_comm t]
        exact div_mul_cancel₀ _ (show 0 < deathRate k + t by linarith [hpos k hk']).ne'
      rw [hsplit]
      calc stoppingProb s b * (∏ k ∈ Ioc b n, deathRate k / (deathRate k + t))
            * ((∏ k ∈ Ioc 1 b, (t + deathRate k)) * ∏ k ∈ Ioc b n, (t + deathRate k))
          = stoppingProb s b * ((∏ k ∈ Ioc b n, deathRate k / (deathRate k + t))
              * ∏ k ∈ Ioc b n, (t + deathRate k)) * ∏ k ∈ Ioc 1 b, (t + deathRate k) := by
            ring
        _ = stoppingProb s b * (∏ k ∈ Ioc b n, deathRate k)
            * ∏ k ∈ Ioc 1 b, (t + deathRate k) := by
            rw [hcancel]
    have heq := congrArg (· * ∏ k ∈ Ioc 1 n, (t + deathRate k)) (hlap t ht)
    simp only [sub_mul, one_mul, sum_mul] at heq
    rw [sum_congr rfl hL, sum_congr rfl hR] at heq
    exact heq
  have heval : ∀ t : ℝ, (∏ k ∈ Ioc 1 n, (Polynomial.X + Polynomial.C (deathRate k))
        - ∑ k ∈ Ioc 1 n, Polynomial.C (spectralCoeff s ⊥ k) * Polynomial.X
            * ∏ j ∈ (Ioc 1 n).erase k, (Polynomial.X + Polynomial.C (deathRate j))
        - ∑ b ∈ Icc 1 n, Polynomial.C (stoppingProb s b * ∏ k ∈ Ioc b n, deathRate k)
            * ∏ k ∈ Ioc 1 b, (Polynomial.X + Polynomial.C (deathRate k))).eval t
      = ∏ k ∈ Ioc 1 n, (t + deathRate k)
        - ∑ k ∈ Ioc 1 n, spectralCoeff s ⊥ k * t * ∏ j ∈ (Ioc 1 n).erase k, (t + deathRate j)
        - ∑ b ∈ Icc 1 n, stoppingProb s b * (∏ k ∈ Ioc b n, deathRate k)
            * ∏ k ∈ Ioc 1 b, (t + deathRate k) := by
    intro t
    simp only [Polynomial.eval_sub, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_prod, Polynomial.eval_add]
  have hzero : (∏ k ∈ Ioc 1 n, (Polynomial.X + Polynomial.C (deathRate k))
        - ∑ k ∈ Ioc 1 n, Polynomial.C (spectralCoeff s ⊥ k) * Polynomial.X
            * ∏ j ∈ (Ioc 1 n).erase k, (Polynomial.X + Polynomial.C (deathRate j))
        - ∑ b ∈ Icc 1 n, Polynomial.C (stoppingProb s b * ∏ k ∈ Ioc b n, deathRate k)
            * ∏ k ∈ Ioc 1 b, (Polynomial.X + Polynomial.C (deathRate k))) = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _
      (Set.Infinite.mono ?_ (Set.Ici_infinite (0 : ℝ)))
    intro t ht
    exact (heval t).trans (sub_eq_zero.mpr (hclear t ht))
  have hat := heval (-deathRate n)
  rw [hzero, Polynomial.eval_zero] at hat
  have hn1 : n ∈ Ioc 1 n := mem_Ioc.mpr ⟨by omega, le_rfl⟩
  have hP0 : ∏ k ∈ Ioc 1 n, (-deathRate n + deathRate k) = 0 :=
    prod_eq_zero hn1 (show -deathRate n + deathRate n = 0 by ring)
  have hS : ∑ k ∈ Ioc 1 n, spectralCoeff s ⊥ k * -deathRate n
        * ∏ j ∈ (Ioc 1 n).erase k, (-deathRate n + deathRate j)
      = spectralCoeff s ⊥ n * -deathRate n
        * ∏ j ∈ Ioc 1 (n - 1), (deathRate j - deathRate n) := by
    rw [sum_eq_single n]
    · have herase : (Ioc 1 n).erase n = Ioc 1 (n - 1) := by
        ext x
        simp only [mem_erase, mem_Ioc]
        omega
      rw [herase]
      congr 1
      exact prod_congr rfl fun j _ ↦ by ring
    · intro k _ hkn
      have hvanish : ∏ j ∈ (Ioc 1 n).erase k, (-deathRate n + deathRate j) = 0 :=
        prod_eq_zero (show n ∈ (Ioc 1 n).erase k from mem_erase.mpr ⟨fun h ↦ hkn h.symm, hn1⟩)
          (show -deathRate n + deathRate n = 0 by ring)
      rw [hvanish, mul_zero]
    · intro hnot
      exact absurd hn1 hnot
  have hB : ∑ b ∈ Icc 1 n, stoppingProb s b * (∏ k ∈ Ioc b n, deathRate k)
        * ∏ k ∈ Ioc 1 b, (-deathRate n + deathRate k)
      = ∑ b ∈ Ico 1 n, stoppingProb s b * (∏ k ∈ Ioc b n, deathRate k)
          * ∏ k ∈ Ioc 1 b, (deathRate k - deathRate n) := by
    rw [sum_eq_sum_diff_singleton_add (mem_Icc.mpr ⟨by omega, le_rfl⟩), hP0, mul_zero, add_zero]
    have hset : Icc 1 n \ {n} = Ico 1 n := by
      ext x
      simp only [mem_sdiff, mem_Icc, mem_Ico, mem_singleton]
      omega
    rw [hset]
    refine sum_congr rfl fun b _ ↦ ?_
    congr 1
    exact prod_congr rfl fun k _ ↦ by ring
  rw [hP0, hS, hB] at hat
  linear_combination -hat

/-- **The residue formula.** For `n ≥ 2`,
`σ_n = ∑_{b=1}^{n-1} p_b ∏_{k=b+1}^{n-1} d_k/(d_k - d_n)`. -/
theorem spectralCoeff_bot_self_eq {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    spectralCoeff s ⊥ n = ∑ b ∈ Ico 1 n,
      stoppingProb s b * ∏ k ∈ Ioc b (n - 1), deathRate k / (deathRate k - deathRate n) := by
  have hE : ∀ a c : ℕ, 1 ≤ a → c ≤ n - 1 → ∏ j ∈ Ioc a c, (deathRate j - deathRate n) ≠ 0 :=
    fun a c ha hc ↦ prod_ne_zero_iff.mpr fun j hj ↦ sub_ne_zero.mpr
      (deathRate_lt_deathRate (by have := (mem_Ioc.mp hj).1; omega)
        (by have := (mem_Ioc.mp hj).2; omega)).ne
  have hdn : deathRate n ≠ 0 := deathRate_ne_zero hn
  have hD : deathRate n * ∏ j ∈ Ioc 1 (n - 1), (deathRate j - deathRate n) ≠ 0 :=
    mul_ne_zero hdn (hE 1 (n - 1) le_rfl le_rfl)
  rw [(eq_div_iff hD).mpr (spectralCoeff_bot_self_mul_eq hn s), sum_div]
  refine sum_congr rfl fun b hb ↦ ?_
  obtain ⟨hb1, hbn⟩ := mem_Ico.mp hb
  have htop : ∏ k ∈ Ioc b n, deathRate k = (∏ k ∈ Ioc b (n - 1), deathRate k) * deathRate n := by
    have h := prod_Ioc_succ_top (show b ≤ n - 1 by omega) deathRate
    rwa [Nat.sub_add_cancel (show 1 ≤ n by omega)] at h
  have hsplit : ∏ j ∈ Ioc 1 (n - 1), (deathRate j - deathRate n)
      = (∏ j ∈ Ioc 1 b, (deathRate j - deathRate n))
        * ∏ j ∈ Ioc b (n - 1), (deathRate j - deathRate n) :=
    (prod_Ioc_consecutive _ hb1 (by omega)).symm
  have h1 := hE 1 b le_rfl (by omega)
  have h2 := hE b (n - 1) hb1 le_rfl
  rw [htop, hsplit, prod_div_distrib]
  field_simp

/-! ### The finite-difference form -/

/-- The ladder residue by downward induction on its lower index. With `N = a + m + 2` fixed,
`C(2N-2, N-1) ∏_{k=a+2}^{N-1} d_k/(d_k - d_N) = (-1)^m C(N-2, a) C(N+a, N-1)`. -/
theorem ladderResidue_mul_choose_aux (m : ℕ) : ∀ a N : ℕ, N = a + m + 2 →
    ((2 * N - 2).choose (N - 1) : ℝ)
        * ∏ k ∈ Ioc (a + 1) (N - 1), deathRate k / (deathRate k - deathRate N)
      = (-1) ^ m * ((N - 2).choose a : ℝ) * ((N + a).choose (N - 1) : ℝ) := by
  induction m with
  | zero =>
    intro a N hN
    rw [show 2 * N - 2 = N + a by omega, show N - 1 = a + 1 by omega, show N - 2 = a by omega]
    simp
  | succ m ih =>
    intro a N hN
    have hsplit : ∏ k ∈ Ioc (a + 1) (N - 1), deathRate k / (deathRate k - deathRate N)
        = deathRate (a + 1 + 1) / (deathRate (a + 1 + 1) - deathRate N)
          * ∏ k ∈ Ioc (a + 1 + 1) (N - 1), deathRate k / (deathRate k - deathRate N) := by
      have hcons := prod_Ioc_consecutive (fun k ↦ deathRate k / (deathRate k - deathRate N))
        (show a + 1 ≤ a + 1 + 1 by omega) (show a + 1 + 1 ≤ N - 1 by omega)
      rw [Nat.Ioc_succ_singleton, prod_singleton] at hcons
      exact hcons.symm
    have hih := ih (a + 1) N (by omega)
    have h1 : (N - 2).choose (a + 1) * (a + 1) = (N - 2).choose a * (m + 1) := by
      have h := Nat.choose_succ_right_eq (N - 2) a
      rwa [show N - 2 - a = m + 1 by omega] at h
    have h2 : (N + a).choose (N - 1) * (N + (a + 1))
        = (N + (a + 1)).choose (N - 1) * (a + 2) := by
      have h := Nat.choose_mul_succ_eq (N + a) (N - 1)
      rwa [show N + a + 1 - (N - 1) = a + 2 by omega, show N + a + 1 = N + (a + 1) by omega] at h
    have h1r : ((N - 2).choose (a + 1) : ℝ) * ((a : ℝ) + 1)
        = ((N - 2).choose a : ℝ) * ((m : ℝ) + 1) := by
      exact_mod_cast h1
    have h2r : ((N + a).choose (N - 1) : ℝ) * ((N : ℝ) + ((a : ℝ) + 1))
        = ((N + (a + 1)).choose (N - 1) : ℝ) * ((a : ℝ) + 2) := by
      exact_mod_cast h2
    have hNr : (N : ℝ) = (a : ℝ) + (m : ℝ) + 3 := by
      rw [hN]
      push_cast
      ring
    have hD : deathRate (a + 1 + 1) - deathRate N ≠ 0 :=
      sub_ne_zero.mpr (deathRate_lt_deathRate (by omega) (by omega)).ne
    have hE : ((m : ℝ) + 1) * ((N : ℝ) + ((a : ℝ) + 1)) ≠ 0 := by positivity
    have hF : deathRate (a + 1 + 1) / (deathRate (a + 1 + 1) - deathRate N)
        = -(((a : ℝ) + 2) * ((a : ℝ) + 1)) / (((m : ℝ) + 1) * ((N : ℝ) + ((a : ℝ) + 1))) := by
      rw [div_eq_div_iff hD hE]
      unfold deathRate Descent.Core.pairCount
      rw [hNr]
      push_cast
      ring
    rw [hsplit, mul_left_comm ((2 * N - 2).choose (N - 1) : ℝ), hih, hF, div_mul_eq_mul_div,
      div_eq_iff hE]
    linear_combination
      (-((-1 : ℝ) ^ m) * ((a : ℝ) + 2) * ((N + (a + 1)).choose (N - 1) : ℝ)) * h1r
        + ((-1 : ℝ) ^ m * ((N - 2).choose a : ℝ) * ((m : ℝ) + 1)) * h2r

/-- **The ladder residue as signed binomials.** For `1 ≤ b < n`,
`C(2n-2, n-1) ∏_{k=b+1}^{n-1} d_k/(d_k - d_n) = (-1)^{n-1-b} C(n-2, b-1) C(n+b-1, n-1)`. -/
theorem ladderResidue_mul_choose {n b : ℕ} (hb : 1 ≤ b) (hbn : b < n) :
    ((2 * n - 2).choose (n - 1) : ℝ)
        * ∏ k ∈ Ioc b (n - 1), deathRate k / (deathRate k - deathRate n)
      = (-1) ^ (n - 1 - b) * ((n - 2).choose (b - 1) : ℝ)
          * ((n + b - 1).choose (n - 1) : ℝ) := by
  obtain ⟨a, rfl⟩ : ∃ a, b = a + 1 := ⟨b - 1, by omega⟩
  rw [show a + 1 - 1 = a by omega, show n + (a + 1) - 1 = n + a by omega]
  exact ladderResidue_mul_choose_aux (n - 1 - (a + 1)) a n (by omega)

/-- **The top coefficient against the central binomial.** For `n ≥ 2`,
`σ_n C(2n-2, n-1) = ∑_{b=1}^{n-1} (-1)^{n-1-b} C(n-2, b-1) p_b C(n+b-1, n-1)`. -/
theorem spectralCoeff_bot_self_mul_choose {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    spectralCoeff s ⊥ n * ((2 * n - 2).choose (n - 1) : ℝ)
      = ∑ b ∈ Ico 1 n, (-1) ^ (n - 1 - b) * ((n - 2).choose (b - 1) : ℝ)
          * (stoppingProb s b * ((n + b - 1).choose (n - 1) : ℝ)) := by
  rw [mul_comm (spectralCoeff s ⊥ n), spectralCoeff_bot_self_eq hn s, mul_sum]
  refine sum_congr rfl fun b hb ↦ ?_
  obtain ⟨hb1, hbn⟩ := mem_Ico.mp hb
  rw [mul_left_comm ((2 * n - 2).choose (n - 1) : ℝ), ladderResidue_mul_choose hb1 hbn]
  ring

/-- **The finite-difference form.** For `n ≥ 2`, `σ_n C(2n-2, n-1) = Δ^{n-2} g (1)`, where
`g(b) = p_b C(n+b-1, n-1)` and `Δ` is the unit forward difference on `ℕ`. -/
theorem spectralCoeff_bot_self_mul_choose_eq_fwdDiff {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    spectralCoeff s ⊥ n * ((2 * n - 2).choose (n - 1) : ℝ)
      = Δ_[1]^[n - 2] (fun b : ℕ ↦ stoppingProb s b * ((n + b - 1).choose (n - 1) : ℝ)) 1 := by
  rw [spectralCoeff_bot_self_mul_choose hn s, fwdDiff_iter_eq_sum_shift, sum_Ico_eq_sum_range,
    show n - 2 + 1 = n - 1 by omega]
  refine sum_congr rfl fun k hk ↦ ?_
  have hk' := mem_range.mp hk
  simp only [zsmul_eq_mul, smul_eq_mul, mul_one]
  rw [show n - 1 - (1 + k) = n - 2 - k by omega, show 1 + k - 1 = k by omega]
  push_cast
  ring

/-! ### The injective interface -/

/-- **An injective interface connects only at the root**: `B = 1` surely. -/
theorem stoppingProb_of_injective {n : ℕ} (hn : 2 ≤ n) {s : Fin n → Fin n}
    (hs : Function.Injective s) (b : ℕ) : stoppingProb s b = if b = 1 then 1 else 0 := by
  haveI : NeZero n := ⟨by omega⟩
  have hF : ∀ k, 2 ≤ k → k ≤ n → connectedProb s k = 0 := by
    intro k hk hkn
    unfold connectedProb
    refine sum_eq_zero fun π hπ ↦ ?_
    have htop : π = ⊤ := by
      have h := (mem_filter.mp hπ).2
      rwa [observed_eq_of_injective hs] at h
    rw [htop, blockLaw_toReal (n - k) (by omega) ⊤,
      if_neg (show ¬blocks (⊤ : ER n) = n - (n - k) by rw [blocks_top]; omega)]
  by_cases hb : b ∈ Icc 1 n
  · obtain ⟨hb1, hbn⟩ := mem_Icc.mp hb
    rcases Nat.lt_or_ge b n with hlt | hge
    · rw [stoppingProb_eq s hb1 hlt, hF (b + 1) (by omega) (by omega), sub_zero]
      by_cases h1 : b = 1
      · subst h1
        rw [if_pos rfl, connectedProb_one s (by omega)]
      · rw [if_neg h1, hF b (by omega) hbn]
    · obtain rfl : b = n := by omega
      rw [stoppingProb_self (by omega) s, hF b hn le_rfl, if_neg (show ¬b = 1 by omega)]
  · rw [if_neg (show ¬b = 1 from fun h ↦ hb (mem_Icc.mpr ⟨by omega, by omega⟩))]
    unfold stoppingProb
    rw [stoppingLaw_eq_zero hn s hb, ENNReal.toReal_zero]

/-- **The top coefficient of an injective interface** is `∏_{k=2}^{n-1} d_k/(d_k - d_n)`. -/
theorem spectralCoeff_bot_self_of_injective {n : ℕ} (hn : 2 ≤ n) {s : Fin n → Fin n}
    (hs : Function.Injective s) :
    spectralCoeff s ⊥ n = ∏ k ∈ Ioc 1 (n - 1), deathRate k / (deathRate k - deathRate n) := by
  rw [spectralCoeff_bot_self_eq hn s, sum_eq_single 1]
  · rw [stoppingProb_of_injective hn hs, if_pos rfl, one_mul]
  · intro b _ hb
    rw [stoppingProb_of_injective hn hs, if_neg hb, zero_mul]
  · intro h
    exact absurd (mem_Ico.mpr ⟨le_rfl, by omega⟩) h

/-- The top coefficient of an injective interface is nonzero. -/
theorem spectralCoeff_bot_self_ne_zero_of_injective {n : ℕ} (hn : 2 ≤ n) {s : Fin n → Fin n}
    (hs : Function.Injective s) : spectralCoeff s ⊥ n ≠ 0 := by
  rw [spectralCoeff_bot_self_of_injective hn hs]
  refine prod_ne_zero_iff.mpr fun k hk ↦ div_ne_zero (deathRate_ne_zero ?_) ?_
  · have := (mem_Ioc.mp hk).1
    omega
  · exact sub_ne_zero.mpr (deathRate_lt_deathRate (by have := (mem_Ioc.mp hk).1; omega)
      (by have := (mem_Ioc.mp hk).2; omega)).ne

/-- **The injective interface: `σ_n = (-1)^n / C_{n-1}`.** For `n ≥ 2`,
`σ_n C(2n-2, n-1) = (-1)^n n`, and `C(2n-2, n-1)/n` is the Catalan number `C_{n-1}`. -/
theorem spectralCoeff_bot_self_mul_choose_of_injective {n : ℕ} (hn : 2 ≤ n) {s : Fin n → Fin n}
    (hs : Function.Injective s) :
    spectralCoeff s ⊥ n * ((2 * n - 2).choose (n - 1) : ℝ) = (-1) ^ n * n := by
  rw [mul_comm (spectralCoeff s ⊥ n), spectralCoeff_bot_self_of_injective hn hs,
    ladderResidue_mul_choose (n := n) le_rfl (by omega)]
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  have hc : (j + 2 + 1 - 1).choose (j + 2 - 1) = j + 2 := by
    rw [show j + 2 + 1 - 1 = j + 1 + 1 by omega, show j + 2 - 1 = j + 1 by omega]
    exact Nat.choose_succ_self_right (j + 1)
  rw [hc, show j + 2 - 1 - 1 = j by omega, show (1 : ℕ) - 1 = 0 from rfl, Nat.choose_zero_right]
  push_cast
  ring

/-- **The clock of injective interfaces names the panel size.** -/
theorem panelSize_eq_of_survivalAt_eq_of_injective {n n' : ℕ} (hn : 2 ≤ n) (hn' : 2 ≤ n')
    {s : Fin n → Fin n} {s' : Fin n' → Fin n'} (hs : Function.Injective s)
    (hs' : Function.Injective s')
    (h : ∀ c : ℝ, 0 ≤ c →
      survivalAt (connectionTimeLaw s ⊥) c = survivalAt (connectionTimeLaw s' ⊥) c) : n = n' :=
  PanelSizeIdentifiability.panelSize_eq_of_survivalAt_eq h
    (spectralCoeff_bot_self_ne_zero_of_injective hn hs)
    (spectralCoeff_bot_self_ne_zero_of_injective hn' hs')

end Descent.Pangenome.GraphCoalescent.PanelSizeTopCoefficient
