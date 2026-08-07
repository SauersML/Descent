/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.DecreaseRate
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# Schweinsberg's theorem: the decrease rate, not the jump rate, decides

`Descent.Coalescent.ThreeSeries` proves coming down from infinity when the reciprocal JUMP
rates are summable, and `Descent.Coalescent.DecreaseRate` explains why that is the wrong
condition for a `Λ`-coalescent: a merger of `k` blocks destroys `k - 1` of them, so the rate at
which the count DECREASES,

  `γ_b = Σ_k (k-1) C(b,k) λ_{b,k}`,

can be far larger than the rate `λ_b` at which it merely jumps.  `totalRate_le_decreaseRate`
records `λ_b ≤ γ_b`, hence `Σγ_b⁻¹ ≤ Σλ_b⁻¹`, so the corpus's condition was STRICTLY STRONGER
than Schweinsberg's and the gap was exactly the levels a multiple merger skips: a jump from
`b` to `b - k + 1` pays one sojourn where a level-by-level argument charges `k - 1` of them.

This file closes that gap, and the closing needs no probability -- only the expected-time
recursion, which is a deterministic identity about the jump chain:

  `h(b) = λ_b⁻¹ + Σ_k p_{b,k} · h(b - k + 1)`,   `h(1) = 0`,

where `h(b)` is the mean time to fall from `b` blocks to one and `p_{b,k}` is the chance the
next merger takes `k` blocks.  `meanTime_le_sum` proves

  `h(b) ≤ Σ_{j=2}^{b} γ_j⁻¹`

by strong induction, and the induction step is an exact cancellation rather than an estimate.
Writing `H(b)` for the right-hand side, the step needs `λ_b⁻¹ ≤ Σ_k p_{b,k}(H(b) - H(b-k+1))`.
Each difference `H(b) - H(b-k+1)` is a sum of `k - 1` terms, every one of them at least
`γ_b⁻¹` because `γ` is non-decreasing, so

  `Σ_k p_{b,k}(H(b) - H(b-k+1)) ≥ γ_b⁻¹ · Σ_k (k-1) p_{b,k} = γ_b⁻¹ · (γ_b/λ_b) = λ_b⁻¹`.

The `k - 1` that the naive argument threw away is precisely the `k - 1` levels the skipped sum
supplies, and the two cancel to an equality.  That is Schweinsberg's theorem: **the sojourn a
multiple merger does not pay is paid by the levels it skips.**

## What is assumed

Three things, each true for a `Λ`-coalescent and none of them about genealogy:
`p` is a probability distribution over merger sizes, its mean displacement is `γ_b/λ_b` (which
is the definition of `γ_b` divided through by `λ_b`), and `γ` is non-decreasing.  The
monotonicity is the one substantive assumption; it holds because a larger sample contains the
smaller one's mergers, and it is what lets the comparison run downwards.

## Main results

- `sum_inv_diff_ge`: `H(b) - H(c) ≥ (b - c)/γ_b`, the skipped levels, counted.
- `meanTime_le_sum`: **`h(b) ≤ Σ_{j=2}^{b} γ_j⁻¹`**, Schweinsberg's bound.
- `meanTime_bddAbove`: hence under `Σγ_b⁻¹ < ∞` the descent times are bounded UNIFORMLY in
  the starting number of blocks, which is coming down from infinity.
- `schweinsberg_comesDownFromInfinity`: stated against the corpus's own criterion.
-/

namespace Coalescent

open Finset

/-! ### The skipped levels, counted -/

/-- **`H(b) - H(c) ≥ (b - c)/γ_b`.**  The difference is a sum of `b - c` reciprocals, each of
them at least `γ_b⁻¹` because `γ` is non-decreasing.  This is the whole of the multiple-merger
correction: a jump that skips `b - c` levels is credited with `b - c` of them. -/
theorem sum_inv_diff_ge {gam : ℕ → ℝ} (hpos : ∀ b : ℕ, 2 ≤ b → 0 < gam b)
    (hmono : ∀ i j : ℕ, 2 ≤ i → i ≤ j → gam i ≤ gam j) {c b : ℕ} (hc : 1 ≤ c) (hcb : c ≤ b) :
    ((b : ℝ) - (c : ℝ)) / gam b
      ≤ (∑ j ∈ Finset.Icc 2 b, 1 / gam j) - ∑ j ∈ Finset.Icc 2 c, 1 / gam j := by
  classical
  rcases Nat.eq_or_lt_of_le hcb with hEq | hlt
  · rw [← hEq]
    simp
  · have hb2 : 2 ≤ b := by omega
    have hgb : 0 < gam b := hpos b hb2
    have hsub : Finset.Icc 2 c ⊆ Finset.Icc 2 b := by
      intro x hx
      have := Finset.mem_Icc.mp hx
      exact Finset.mem_Icc.mpr ⟨this.1, by omega⟩
    have hsdiff : Finset.Icc 2 b \ Finset.Icc 2 c = Finset.Icc (c + 1) b := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_Icc]
      omega
    have hsplit : (∑ j ∈ Finset.Icc 2 b, 1 / gam j) - ∑ j ∈ Finset.Icc 2 c, 1 / gam j
        = ∑ j ∈ Finset.Icc (c + 1) b, 1 / gam j := by
      rw [← hsdiff, Finset.sum_sdiff_eq_sub hsub]
    rw [hsplit]
    have hterm : ∀ j ∈ Finset.Icc (c + 1) b, 1 / gam b ≤ 1 / gam j := by
      intro j hj
      have hj' := Finset.mem_Icc.mp hj
      have hj2 : 2 ≤ j := by omega
      exact one_div_le_one_div_of_le (hpos j hj2) (hmono j b hj2 hj'.2)
    have hcard : (Finset.Icc (c + 1) b).card = b - c := by
      rw [Nat.card_Icc]
      omega
    have hlow := Finset.card_nsmul_le_sum (Finset.Icc (c + 1) b) (fun j ↦ 1 / gam j)
      (1 / gam b) hterm
    rw [hcard, nsmul_eq_mul] at hlow
    refine le_trans (le_of_eq ?_) hlow
    have hcast : ((b - c : ℕ) : ℝ) = (b : ℝ) - (c : ℝ) := by
      have : c ≤ b := le_of_lt hlt
      push_cast [Nat.cast_sub this]
      ring
    rw [hcast, div_eq_mul_one_div]

/-! ### Schweinsberg's bound -/

/-- **Schweinsberg's bound: the mean descent time from `b` blocks is at most `Σ_{j=2}^b γ_j⁻¹`.**

Strong induction on `b`.  The base `b = 1` is `h(1) = 0` against an empty sum.  The step is the
cancellation described in this module's header: the sojourn `λ_b⁻¹` that a multiple merger
fails to pay is exactly recovered from the `k - 1` levels it skips, because
`Σ_k (k-1) p_{b,k} = γ_b/λ_b` by the definition of the decrease rate.

Nothing here is an inequality except `γ`'s monotonicity: the drift identity turns the estimate
into an equality at the last step, which is why the bound is `Σγ_j⁻¹` and not a multiple of
it. -/
theorem meanTime_le_sum {h gam lamb : ℕ → ℝ} {p : ℕ → ℕ → ℝ}
    (hpos : ∀ b : ℕ, 2 ≤ b → 0 < gam b) (hmono : ∀ i j : ℕ, 2 ≤ i → i ≤ j → gam i ≤ gam j)
    (hlamb : ∀ b : ℕ, 2 ≤ b → 0 < lamb b)
    (hp0 : ∀ b k : ℕ, 0 ≤ p b k)
    (hp1 : ∀ b : ℕ, 2 ≤ b → ∑ k ∈ Finset.Icc 2 b, p b k = 1)
    (hdrift : ∀ b : ℕ, 2 ≤ b → ∑ k ∈ Finset.Icc 2 b, ((k : ℝ) - 1) * p b k = gam b / lamb b)
    (h1 : h 1 = 0)
    (hrec : ∀ b : ℕ, 2 ≤ b → h b = 1 / lamb b + ∑ k ∈ Finset.Icc 2 b, p b k * h (b - k + 1))
    (b : ℕ) (hb : 1 ≤ b) : h b ≤ ∑ j ∈ Finset.Icc 2 b, 1 / gam j := by
  classical
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    rcases Nat.lt_or_ge b 2 with hb1 | hb2
    · have : b = 1 := by omega
      subst this
      simp [h1]
    · -- the inductive bound on each successor state
      have hstep : ∀ k ∈ Finset.Icc 2 b,
          p b k * h (b - k + 1) ≤ p b k * ∑ j ∈ Finset.Icc 2 (b - k + 1), 1 / gam j := by
        intro k hk
        have hk' := Finset.mem_Icc.mp hk
        have hlt : b - k + 1 < b := by omega
        have hge : 1 ≤ b - k + 1 := by omega
        exact mul_le_mul_of_nonneg_left (ih _ hlt hge) (hp0 b k)
      -- the cancellation
      have hgb : 0 < gam b := hpos b hb2
      have hlb : 0 < lamb b := hlamb b hb2
      set H : ℕ → ℝ := fun c ↦ ∑ j ∈ Finset.Icc 2 c, 1 / gam j with hH
      have hgap : ∀ k ∈ Finset.Icc 2 b,
          p b k * H (b - k + 1) ≤ p b k * H b - p b k * (((k : ℝ) - 1) * (1 / gam b)) := by
        intro k hk
        have hk' := Finset.mem_Icc.mp hk
        have hc1 : 1 ≤ b - k + 1 := by omega
        have hcb : b - k + 1 ≤ b := by omega
        have hd := sum_inv_diff_ge hpos hmono (c := b - k + 1) (b := b) hc1 hcb
        have hcast : (b : ℝ) - ((b - k + 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
          have hbk : b - k + 1 = b + 1 - k := by omega
          rw [hbk]
          have hkb : k ≤ b + 1 := by omega
          push_cast [Nat.cast_sub hkb]
          ring
        rw [hcast] at hd
        have hd' : ((k : ℝ) - 1) * (1 / gam b)
            ≤ (∑ j ∈ Finset.Icc 2 b, 1 / gam j)
              - ∑ j ∈ Finset.Icc 2 (b - k + 1), 1 / gam j := by
          rw [← div_eq_mul_one_div]
          exact hd
        have hres : ((k : ℝ) - 1) * (1 / gam b) ≤ H b - H (b - k + 1) := hd'
        nlinarith [hp0 b k]
      -- assemble
      have hsum : ∑ k ∈ Finset.Icc 2 b, p b k * h (b - k + 1)
          ≤ ∑ k ∈ Finset.Icc 2 b, (p b k * H b - p b k * (((k : ℝ) - 1) * (1 / gam b))) := by
        refine Finset.sum_le_sum fun k hk ↦ ?_
        exact le_trans (hstep k hk) (hgap k hk)
      have hexp : ∑ k ∈ Finset.Icc 2 b, (p b k * H b - p b k * (((k : ℝ) - 1) * (1 / gam b)))
          = (∑ k ∈ Finset.Icc 2 b, p b k) * H b
            - (∑ k ∈ Finset.Icc 2 b, ((k : ℝ) - 1) * p b k) * (1 / gam b) := by
        rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ ↦ by ring
      rw [hexp, hp1 b hb2, hdrift b hb2, one_mul] at hsum
      have hcancel : gam b / lamb b * (1 / gam b) = 1 / lamb b := by
        field_simp
      rw [hcancel] at hsum
      rw [hrec b hb2]
      have : H b = ∑ j ∈ Finset.Icc 2 b, 1 / gam j := rfl
      linarith

/-! ### Coming down from infinity -/

/-- **Under `Σγ_b⁻¹ < ∞` the descent times are bounded UNIFORMLY in the number of blocks.**
That uniformity is what coming down from infinity means: no matter how many lineages the
process starts with, it reaches one in bounded expected time, so it can be started from
infinitely many. -/
theorem meanTime_bddAbove {h gam lamb : ℕ → ℝ} {p : ℕ → ℕ → ℝ}
    (hpos : ∀ b : ℕ, 2 ≤ b → 0 < gam b) (hmono : ∀ i j : ℕ, 2 ≤ i → i ≤ j → gam i ≤ gam j)
    (hlamb : ∀ b : ℕ, 2 ≤ b → 0 < lamb b)
    (hp0 : ∀ b k : ℕ, 0 ≤ p b k)
    (hp1 : ∀ b : ℕ, 2 ≤ b → ∑ k ∈ Finset.Icc 2 b, p b k = 1)
    (hdrift : ∀ b : ℕ, 2 ≤ b → ∑ k ∈ Finset.Icc 2 b, ((k : ℝ) - 1) * p b k = gam b / lamb b)
    (h1 : h 1 = 0)
    (hrec : ∀ b : ℕ, 2 ≤ b → h b = 1 / lamb b + ∑ k ∈ Finset.Icc 2 b, p b k * h (b - k + 1))
    (hcdi : comesDownFromInfinity gam) :
    ∀ b, 1 ≤ b → h b ≤ ∑' i : ℕ, 1 / gam (i + 2) := by
  classical
  intro b hb
  refine le_trans (meanTime_le_sum hpos hmono hlamb hp0 hp1 hdrift h1 hrec b hb) ?_
  have hreindex : ∑ j ∈ Finset.Icc 2 b, 1 / gam j
      = ∑ i ∈ Finset.range (b - 1), 1 / gam (i + 2) := by
    rw [← Nat.Ico_succ_right, Finset.sum_Ico_eq_sum_range]
    have hr : b + 1 - 2 = b - 1 := by omega
    rw [hr]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [Nat.add_comm]
  rw [hreindex]
  have hnn : ∀ i : ℕ, 0 ≤ 1 / gam (i + 2) := by
    intro i
    have := hpos (i + 2) (by omega)
    positivity
  exact sum_le_tsum _ (fun i _ ↦ hnn i) hcdi

/-- **Schweinsberg's theorem, stated against the corpus's own criterion.**  The condition that
decides coming down is summability of the reciprocal DECREASE rates -- not of the reciprocal
jump rates, which `DecreaseRate.comesDownFromInfinity_of_summable_totalRate` shows is strictly
stronger.

    Empirical status: NOT AN EMPIRICAL CLAIM -- a theorem about the jump chain's mean
    times.  Which rates a population's genealogy has is the empirical question, and
    `Blindness.MultipleMergerBlindness` records which statistics could tell. -/
theorem schweinsberg_comesDownFromInfinity {h lamb : ℕ → ℝ} {lam : ℕ → ℕ → ℝ} {p : ℕ → ℕ → ℝ}
    (hpos : ∀ b : ℕ, 2 ≤ b → 0 < decreaseRate lam b)
    (hmono : ∀ i j : ℕ, 2 ≤ i → i ≤ j → decreaseRate lam i ≤ decreaseRate lam j)
    (hlamb : ∀ b : ℕ, 2 ≤ b → 0 < lamb b)
    (hp0 : ∀ b k : ℕ, 0 ≤ p b k)
    (hp1 : ∀ b : ℕ, 2 ≤ b → ∑ k ∈ Finset.Icc 2 b, p b k = 1)
    (hdrift : ∀ b : ℕ, 2 ≤ b →
      ∑ k ∈ Finset.Icc 2 b, ((k : ℝ) - 1) * p b k = decreaseRate lam b / lamb b)
    (h1 : h 1 = 0)
    (hrec : ∀ b : ℕ, 2 ≤ b → h b = 1 / lamb b + ∑ k ∈ Finset.Icc 2 b, p b k * h (b - k + 1))
    (hcdi : comesDownFromInfinity (decreaseRate lam)) :
    ∃ M : ℝ, ∀ b, 1 ≤ b → h b ≤ M :=
  ⟨_, meanTime_bddAbove hpos hmono hlamb hp0 hp1 hdrift h1 hrec hcdi⟩

end Coalescent

end Descent
