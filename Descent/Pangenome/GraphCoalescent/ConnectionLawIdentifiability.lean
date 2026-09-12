/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ReportedConnectionLadder
import Descent.Pangenome.GraphCoalescent.ReportedConnectionSpectrum
import Descent.Pangenome.GraphCoalescent.ReportedConnectionTies
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# What the law of the reported connection time identifies

The identifiability question for the pangenome hidden-clock note asks whether the law of the
reported connection time `τ_q`, or the connectivity cumulant `C_c(z)`, determines the multiset of
fiber sizes. This file settles the analytic half. For two interfaces `s, s'` on one panel of `n`
individuals, the law of `τ_q` and the cumulant carry the same information: each determines the
other. So the clock can answer a question about the fiber sizes only through `C_c`.

## The chain of equivalences

- `eq_zero_of_sum_mul_prod_Ioc`: the ladder transforms `∏_{k=b+1}^{n} d_k/(d_k + θ)`,
  `b = 1, …, n`, are linearly independent on `θ ≥ 0`. Clearing denominators gives a polynomial
  in `θ` that vanishes on `[0, ∞)`, hence everywhere. At `θ = -d_{b+1}` every term above `b`
  vanishes, which isolates the coefficient of `b` once the lower ones are known to be zero.
- `stoppingProb_eq_of_laplace_eq`, `laplace_eq_of_stoppingProb_eq`: by (D7) the transform of
  `τ_q` determines the law `p_b` of the number `B` of true lineages at first connection, and
  conversely.
- `connectedProb_eq_of_stoppingProb_eq`, `stoppingProb_eq_of_connectedProb_eq`: by (D6), `p_b`
  and the level probabilities `F_k` determine each other, `F_n = p_n` and `F_b = p_b + F_{b+1}`.
- `connectivityCumulant_eq_of_connectedProb_eq`, `connectedProb_eq_of_connectivityCumulant_eq`:
  by (D5), `F_k = a_{n,k} [z^k] C_c` with `a_{n,k} ≠ 0`, and the cumulant has no coefficient
  outside `1, …, n` (`coeff_connectivityCumulant_graphKer_eq_zero`).
- `laplace_eq_iff_connectivityCumulant_eq`: the transform on `θ ≥ 0` is equivalent to the
  cumulant. `map_connectionTime_eq_iff_connectivityCumulant_eq`: so is the law of `τ_q` under
  the path law of `ReportedConnectionClock`, since that law is the mixture over `B` of the
  Kingman ladder laws (`map_connectionTime_apply`).

## The spectral coefficients and the first-step law

- `eq_zero_of_sum_mul_exp_deathRate`: Kingman's exponentials `e^{-d_k c}`, `k = 2, …, n`, are
  linearly independent on `c ≥ 0`. Since `d_k = C(k, 2)` is a natural number, a combination of
  them is a polynomial in `y = e^{-c}`, and it vanishes on `(0, 1]`.
- `spectralCoeff_eq_iff_survivalAt_eq`: the survival function of the first-step law
  `connectionTimeLaw s ⊥` carries exactly its spectral coefficients `spectralCoeff s ⊥ k`.
- `connectionLaplace_bot_eq_sum_stoppingProb`: the first-step transform at `⊥` is (D7),
  `connectionLaplace s t ⊥ = ∑_b p_b ∏_{k=b+1}^{n} d_k/(d_k + t)`. The backward equation unrolls
  along the head law of the jump chain one level at a time (`sum_blockLaw_connectionLaplace_succ`).
  At level `m` the paths that have already connected contribute `p_b ∏_{k>b} d_k/(d_k + t)` for
  `b ≥ m`. An unconnected state carries the factor `∏_{k>m} d_k/(d_k + t)` times its own
  transform, and one more jump either connects it, with probability `p_{m-1}`, or passes it on.
- `lintegral_exp_connectionTimeLaw_bot_eq_laplace`: so the first-step law and the path law have
  the same Laplace transform at every `t ≥ 0`. `ReportedConnectionTies` identifies their means.
- `connectionLaplace_eq_one_sub_sum_spectralCoeff`: from every state the first-step transform is
  `1 - ∑_k spectralCoeff s ξ k · t/(t + d_k)`. The induction along covers is the recursion of the
  spectral coefficients read through the partial fractions
  `d_K/(d_K + t) · t/(t + d_k) = d_K/(d_K - d_k) · (t/(t + d_k) - t/(t + d_K))`.
- `eq_zero_of_sum_mul_div_add_deathRate`: the partial fractions `t/(t + d_k)`, `k = 2, …, n`, are
  linearly independent on `t ≥ 0`, by clearing denominators and evaluating at `t = -d_m`.
- `spectralCoeff_eq_iff_connectivityCumulant_eq`, `survivalAt_eq_iff_connectivityCumulant_eq`,
  `connectionTimeLaw_bot_eq_iff_connectivityCumulant_eq`: the spectral coefficients, the survival
  function and the first-step law are each equivalent to the cumulant. A survival function on
  `[0, ∞)` determines the law (`connectionTimeLaw_bot_eq_of_survivalAt_eq`), the law determines
  the transform, the transform determines the cumulant through (D7), and the cumulant gives back
  the transform and so the spectral coefficients.

## What is narrower

The panel size `n` is fixed: both interfaces act on `Fin n`, and whether the law of `τ_q` alone
determines `n` is not addressed. Whether `C_c` determines the multiset of fiber sizes is the
combinatorial half of the question and is not in this file.

## Empirical status

None. Every declaration is an identity or an implication between laws built from the corpus jump
chain and holding times, finite sums and polynomials, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.ConnectionLawIdentifiability

open Coalescent Finset MeasureTheory
open scoped Classical ENNReal NNReal

/-! ### The ladder transforms are linearly independent -/

/-- **The ladder transforms are linearly independent.** If
`∑_{b=1}^{n} δ_b ∏_{k=b+1}^{n} d_k/(d_k + θ)` vanishes for every `θ ≥ 0`, then every `δ_b` is
zero. -/
theorem eq_zero_of_sum_mul_prod_Ioc {n : ℕ} {δ : ℕ → ℝ}
    (h : ∀ θ : ℝ, 0 ≤ θ →
      ∑ b ∈ Icc 1 n, δ b * ∏ k ∈ Ioc b n, deathRate k / (deathRate k + θ) = 0) :
    ∀ b ∈ Icc 1 n, δ b = 0 := by
  have hclear : ∀ θ : ℝ, 0 ≤ θ →
      ∑ b ∈ Icc 1 n, δ b * (∏ k ∈ Ioc b n, deathRate k) * ∏ k ∈ Ioc 1 b, (θ + deathRate k)
        = 0 := by
    intro θ hθ
    have hpos : ∀ k ∈ Ioc 1 n, 0 < deathRate k + θ := fun k hk ↦
      add_pos_of_pos_of_nonneg (deathRate_pos (by have := (mem_Ioc.mp hk).1; omega)) hθ
    have hterm : ∀ b ∈ Icc 1 n,
        δ b * (∏ k ∈ Ioc b n, deathRate k / (deathRate k + θ))
            * ∏ k ∈ Ioc 1 n, (deathRate k + θ)
          = δ b * (∏ k ∈ Ioc b n, deathRate k) * ∏ k ∈ Ioc 1 b, (θ + deathRate k) := by
      intro b hb
      obtain ⟨hb1, hbn⟩ := mem_Icc.mp hb
      have hsplit : ∏ k ∈ Ioc 1 n, (deathRate k + θ)
          = (∏ k ∈ Ioc 1 b, (deathRate k + θ)) * ∏ k ∈ Ioc b n, (deathRate k + θ) :=
        (prod_Ioc_consecutive _ hb1 hbn).symm
      have hcancel : (∏ k ∈ Ioc b n, deathRate k / (deathRate k + θ))
            * ∏ k ∈ Ioc b n, (deathRate k + θ) = ∏ k ∈ Ioc b n, deathRate k := by
        rw [← prod_mul_distrib]
        refine prod_congr rfl fun k hk ↦ div_mul_cancel₀ _ (hpos k ?_).ne'
        exact mem_Ioc.mpr ⟨by have := (mem_Ioc.mp hk).1; omega, (mem_Ioc.mp hk).2⟩
      have hcomm : ∏ k ∈ Ioc 1 b, (deathRate k + θ) = ∏ k ∈ Ioc 1 b, (θ + deathRate k) :=
        prod_congr rfl fun k _ ↦ add_comm _ _
      calc δ b * (∏ k ∈ Ioc b n, deathRate k / (deathRate k + θ))
            * ∏ k ∈ Ioc 1 n, (deathRate k + θ)
          = δ b * ((∏ k ∈ Ioc b n, deathRate k / (deathRate k + θ))
              * ∏ k ∈ Ioc b n, (deathRate k + θ)) * ∏ k ∈ Ioc 1 b, (deathRate k + θ) := by
            rw [hsplit]
            ring
        _ = δ b * (∏ k ∈ Ioc b n, deathRate k) * ∏ k ∈ Ioc 1 b, (θ + deathRate k) := by
            rw [hcancel, hcomm]
    calc ∑ b ∈ Icc 1 n, δ b * (∏ k ∈ Ioc b n, deathRate k) * ∏ k ∈ Ioc 1 b, (θ + deathRate k)
        = ∑ b ∈ Icc 1 n, δ b * (∏ k ∈ Ioc b n, deathRate k / (deathRate k + θ))
            * ∏ k ∈ Ioc 1 n, (deathRate k + θ) := (sum_congr rfl hterm).symm
      _ = (∑ b ∈ Icc 1 n, δ b * ∏ k ∈ Ioc b n, deathRate k / (deathRate k + θ))
            * ∏ k ∈ Ioc 1 n, (deathRate k + θ) := by rw [sum_mul]
      _ = 0 := by rw [h θ hθ, zero_mul]
  have heval : ∀ θ : ℝ, (∑ b ∈ Icc 1 n, Polynomial.C (δ b * ∏ k ∈ Ioc b n, deathRate k)
        * ∏ k ∈ Ioc 1 b, (Polynomial.X + Polynomial.C (deathRate k))).eval θ
      = ∑ b ∈ Icc 1 n, δ b * (∏ k ∈ Ioc b n, deathRate k) * ∏ k ∈ Ioc 1 b, (θ + deathRate k) := by
    intro θ
    simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X]
  have hzero : (∑ b ∈ Icc 1 n, Polynomial.C (δ b * ∏ k ∈ Ioc b n, deathRate k)
      * ∏ k ∈ Ioc 1 b, (Polynomial.X + Polynomial.C (deathRate k))) = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _
      (Set.Infinite.mono ?_ (Set.Ici_infinite (0 : ℝ)))
    intro θ hθ
    exact (heval θ).trans (hclear θ hθ)
  have hall : ∀ θ : ℝ,
      ∑ b ∈ Icc 1 n, δ b * (∏ k ∈ Ioc b n, deathRate k) * ∏ k ∈ Ioc 1 b, (θ + deathRate k)
        = 0 := by
    intro θ
    rw [← heval, hzero, Polynomial.eval_zero]
  have hlow : ∀ j b : ℕ, 1 ≤ b → b ≤ j → b ≤ n → δ b = 0 := by
    intro j
    induction j with
    | zero => intro b hb1 hbj _; omega
    | succ j ih =>
      intro b hb1 hbj hbn
      rcases Nat.lt_or_ge b (j + 1) with hlt | hge
      · exact ih b hb1 (by omega) hbn
      · obtain rfl : b = j + 1 := by omega
        have hev := hall (-deathRate (j + 2))
        rw [sum_eq_single (j + 1)] at hev
        · have hA : ∏ k ∈ Ioc (j + 1) n, deathRate k ≠ 0 :=
            prod_ne_zero_iff.mpr fun k hk ↦
              deathRate_ne_zero (by have := (mem_Ioc.mp hk).1; omega)
          have hP : ∏ k ∈ Ioc 1 (j + 1), (-deathRate (j + 2) + deathRate k) ≠ 0 := by
            refine prod_ne_zero_iff.mpr fun k hk ↦ ?_
            have h1 := (mem_Ioc.mp hk).1
            have h2 := (mem_Ioc.mp hk).2
            have hlt := deathRate_lt_deathRate (show 1 ≤ k by omega) (show k < j + 2 by omega)
            exact (show -deathRate (j + 2) + deathRate k < 0 by linarith).ne
          rcases mul_eq_zero.mp hev with h' | h'
          · exact (mul_eq_zero.mp h').resolve_right hA
          · exact absurd h' hP
        · intro i hi hne
          obtain ⟨hi1, hin⟩ := mem_Icc.mp hi
          rcases Nat.lt_or_ge i (j + 1) with hlt | hge'
          · rw [ih i hi1 (by omega) hin, zero_mul, zero_mul]
          · have hvanish : ∏ k ∈ Ioc 1 i, (-deathRate (j + 2) + deathRate k) = 0 :=
              prod_eq_zero (show j + 2 ∈ Ioc 1 i from mem_Ioc.mpr ⟨by omega, by omega⟩)
                (show -deathRate (j + 2) + deathRate (j + 2) = 0 by ring)
            rw [hvanish, mul_zero]
        · intro hnot
          exact absurd (mem_Icc.mpr ⟨hb1, hbn⟩) hnot
  exact fun b hb ↦ hlow b b (mem_Icc.mp hb).1 le_rfl (mem_Icc.mp hb).2

/-! ### The transform, the stopping level and the level probabilities -/

/-- **The Laplace transform of `τ_q` determines the law of `B`.** If two interfaces on `n ≥ 2`
individuals give the same transform `E e^{-θ τ_q}` at every `θ ≥ 0`, they have the same
first-connection law `p_b`. -/
theorem stoppingProb_eq_of_laplace_eq {n : ℕ} (hn : 2 ≤ n) {s s' : Fin n → Fin n}
    (h : ∀ θ : ℝ, 0 ≤ θ →
      ∫⁻ p, ENNReal.ofReal (Real.exp (-(θ * connectionTime s p))) ∂(trajectoryClockLaw n)
        = ∫⁻ p, ENNReal.ofReal (Real.exp (-(θ * connectionTime s' p))) ∂(trajectoryClockLaw n))
    (b : ℕ) : stoppingProb s b = stoppingProb s' b := by
  by_cases hb : b ∈ Icc 1 n
  · have hreal : ∀ θ : ℝ, 0 ≤ θ →
        ∑ i ∈ Icc 1 n, (stoppingProb s i - stoppingProb s' i)
          * ∏ k ∈ Ioc i n, deathRate k / (deathRate k + θ) = 0 := by
      intro θ hθ
      have hnn : ∀ u : Fin n → Fin n, 0 ≤ ∑ i ∈ Icc 1 n,
          stoppingProb u i * ∏ k ∈ Ioc i n, deathRate k / (deathRate k + θ) := fun u ↦
        sum_nonneg fun i hi ↦ mul_nonneg ENNReal.toReal_nonneg (prod_nonneg fun k hk ↦ by
          have hd := deathRate_pos (show 2 ≤ k by
            have h1 := (mem_Icc.mp hi).1
            have h2 := (mem_Ioc.mp hk).1
            omega)
          exact div_nonneg hd.le (add_nonneg hd.le hθ))
      have heq := h θ hθ
      rw [connectionTime_laplace hn s hθ, connectionTime_laplace hn s' hθ,
        ENNReal.ofReal_eq_ofReal_iff (hnn s) (hnn s')] at heq
      calc ∑ i ∈ Icc 1 n, (stoppingProb s i - stoppingProb s' i)
            * ∏ k ∈ Ioc i n, deathRate k / (deathRate k + θ)
          = ∑ i ∈ Icc 1 n, stoppingProb s i * ∏ k ∈ Ioc i n, deathRate k / (deathRate k + θ)
            - ∑ i ∈ Icc 1 n,
                stoppingProb s' i * ∏ k ∈ Ioc i n, deathRate k / (deathRate k + θ) := by
            rw [← sum_sub_distrib]
            exact sum_congr rfl fun i _ ↦ sub_mul _ _ _
        _ = 0 := by rw [heq, sub_self]
    exact sub_eq_zero.mp
      (eq_zero_of_sum_mul_prod_Ioc (δ := fun i ↦ stoppingProb s i - stoppingProb s' i) hreal b hb)
  · unfold stoppingProb
    rw [stoppingLaw_eq_zero hn s hb, stoppingLaw_eq_zero hn s' hb]

/-- The law of `B` determines the Laplace transform of `τ_q`, by (D7). -/
theorem laplace_eq_of_stoppingProb_eq {n : ℕ} (hn : 2 ≤ n) {s s' : Fin n → Fin n}
    (h : ∀ b, stoppingProb s b = stoppingProb s' b) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∫⁻ p, ENNReal.ofReal (Real.exp (-(θ * connectionTime s p))) ∂(trajectoryClockLaw n)
      = ∫⁻ p, ENNReal.ofReal (Real.exp (-(θ * connectionTime s' p))) ∂(trajectoryClockLaw n) := by
  rw [connectionTime_laplace hn s hθ, connectionTime_laplace hn s' hθ]
  simp only [h]

/-- **The law of `B` determines the level probabilities**, through `F_n = p_n` and
`F_b = p_b + F_{b+1}`. -/
theorem connectedProb_eq_of_stoppingProb_eq {n : ℕ} {s s' : Fin n → Fin n}
    (h : ∀ b, stoppingProb s b = stoppingProb s' b) :
    ∀ k, 1 ≤ k → k ≤ n → connectedProb s k = connectedProb s' k := by
  have key : ∀ i k, k + i = n → 1 ≤ k → connectedProb s k = connectedProb s' k := by
    intro i
    induction i with
    | zero =>
      intro k hki hk
      obtain rfl : k = n := by omega
      rw [← stoppingProb_self hk s, ← stoppingProb_self hk s', h]
    | succ i ih =>
      intro k hki hk
      have hkn : k < n := by omega
      have hs := stoppingProb_eq s hk hkn
      have hs' := stoppingProb_eq s' hk hkn
      have hnext := ih (k + 1) (by omega) (by omega)
      rw [h k] at hs
      linarith
  intro k hk hkn
  exact key (n - k) k (by omega) hk

/-- The level probabilities determine the law of `B`, by (D6). -/
theorem stoppingProb_eq_of_connectedProb_eq {n : ℕ} (hn : 2 ≤ n) {s s' : Fin n → Fin n}
    (h : ∀ k, 1 ≤ k → k ≤ n → connectedProb s k = connectedProb s' k) (b : ℕ) :
    stoppingProb s b = stoppingProb s' b := by
  by_cases hb : b ∈ Icc 1 n
  · obtain ⟨hb1, hbn⟩ := mem_Icc.mp hb
    rcases Nat.lt_or_ge b n with hlt | hge
    · rw [stoppingProb_eq s hb1 hlt, stoppingProb_eq s' hb1 hlt, h b hb1 hbn,
        h (b + 1) (by omega) (by omega)]
    · obtain rfl : b = n := by omega
      rw [stoppingProb_self hb1 s, stoppingProb_self hb1 s', h b hb1 le_rfl]
  · unfold stoppingProb
    rw [stoppingLaw_eq_zero hn s hb, stoppingLaw_eq_zero hn s' hb]

/-! ### The level probabilities and the cumulant -/

/-- **(D5) on the path law**: `F_k = a_{n,k} [z^k] C_q` for `1 ≤ k ≤ n`. -/
theorem connectedProb_eq_jumpCoeff_mul_coeff {n k : ℕ} (s : Fin n → Fin n) (hk : 1 ≤ k)
    (hkn : k ≤ n) :
    connectedProb s k = jumpCoeff n k
      * ((connectivityCumulant (Finpartition.ofSetoid (graphKer s))).coeff k : ℝ) := by
  rw [connectedProb_eq_reportConnectedProbability,
    reportConnectedProbability_eq_connectedByLevel s hk hkn]
  rfl

/-- The cumulant of an interface on `n ≥ 1` individuals has no coefficient outside `1, …, n`:
every state has between one and `n` blocks. -/
theorem coeff_connectivityCumulant_graphKer_eq_zero {n : ℕ} [NeZero n] (s : Fin n → Fin n)
    {k : ℕ} (hk : k ∉ Icc 1 n) :
    (connectivityCumulant (Finpartition.ofSetoid (graphKer s))).coeff k = 0 := by
  rw [coeff_connectivityCumulant_graphKer s (NeZero.pos n) k, Nat.cast_eq_zero]
  refine sum_eq_zero fun π hπ ↦ absurd ?_ hk
  rw [← (mem_filter.mp hπ).2.1]
  exact mem_Icc.mpr ⟨blocks_pos π, (blocks_antitone bot_le).trans_eq (blocks_bot n)⟩

/-- **The level probabilities determine the cumulant.** -/
theorem connectivityCumulant_eq_of_connectedProb_eq {n : ℕ} [NeZero n] {s s' : Fin n → Fin n}
    (h : ∀ k, 1 ≤ k → k ≤ n → connectedProb s k = connectedProb s' k) :
    connectivityCumulant (Finpartition.ofSetoid (graphKer s))
      = connectivityCumulant (Finpartition.ofSetoid (graphKer s')) := by
  ext k
  by_cases hk : k ∈ Icc 1 n
  · obtain ⟨hk1, hkn⟩ := mem_Icc.mp hk
    have hne : jumpCoeff n k ≠ 0 := left_ne_zero_of_mul_eq_one (jumpCoeff_mul_lahNumber hk1 hkn)
    have hF := h k hk1 hkn
    rw [connectedProb_eq_jumpCoeff_mul_coeff s hk1 hkn,
      connectedProb_eq_jumpCoeff_mul_coeff s' hk1 hkn] at hF
    exact_mod_cast mul_left_cancel₀ hne hF
  · rw [coeff_connectivityCumulant_graphKer_eq_zero s hk,
      coeff_connectivityCumulant_graphKer_eq_zero s' hk]

/-- The cumulant determines the level probabilities, by (D5). -/
theorem connectedProb_eq_of_connectivityCumulant_eq {n : ℕ} {s s' : Fin n → Fin n}
    (h : connectivityCumulant (Finpartition.ofSetoid (graphKer s))
      = connectivityCumulant (Finpartition.ofSetoid (graphKer s'))) :
    ∀ k, 1 ≤ k → k ≤ n → connectedProb s k = connectedProb s' k := by
  intro k hk hkn
  rw [connectedProb_eq_jumpCoeff_mul_coeff s hk hkn, connectedProb_eq_jumpCoeff_mul_coeff s' hk hkn,
    h]

/-! ### The law of `τ_q` is the cumulant -/

/-- **The Laplace transform of `τ_q` is equivalent to the connectivity cumulant.** For two
interfaces on `n ≥ 2` individuals, `E e^{-θ τ_q}` agrees at every `θ ≥ 0` exactly when the two
cumulants are equal polynomials. -/
theorem laplace_eq_iff_connectivityCumulant_eq {n : ℕ} (hn : 2 ≤ n) (s s' : Fin n → Fin n) :
    (∀ θ : ℝ, 0 ≤ θ →
      ∫⁻ p, ENNReal.ofReal (Real.exp (-(θ * connectionTime s p))) ∂(trajectoryClockLaw n)
        = ∫⁻ p, ENNReal.ofReal (Real.exp (-(θ * connectionTime s' p))) ∂(trajectoryClockLaw n))
      ↔ connectivityCumulant (Finpartition.ofSetoid (graphKer s))
        = connectivityCumulant (Finpartition.ofSetoid (graphKer s')) := by
  haveI : NeZero n := ⟨by omega⟩
  constructor
  · intro h
    exact connectivityCumulant_eq_of_connectedProb_eq
      (connectedProb_eq_of_stoppingProb_eq (stoppingProb_eq_of_laplace_eq hn h))
  · intro h θ hθ
    exact laplace_eq_of_stoppingProb_eq hn
      (stoppingProb_eq_of_connectedProb_eq hn (connectedProb_eq_of_connectivityCumulant_eq h)) hθ

/-- The reported connection time is a measurable function of the path. -/
theorem measurable_connectionTime {n : ℕ} (s : Fin n → Fin n) : Measurable (connectionTime s) := by
  have hswap : Measurable fun q : (ℕ → ℝ) × List (ER n) ↦
      ∑ j ∈ Ico (stoppingLevel s q.2 - 1) (n - 1), q.1 j :=
    measurable_from_prod_countable_left fun l ↦
      show Measurable fun x : ℕ → ℝ ↦ ∑ j ∈ Ico (stoppingLevel s l - 1) (n - 1), x j from
        Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j
  exact hswap.comp measurable_swap

/-- **The law of `τ_q` is the mixture over `B` of the Kingman ladder laws**: a measurable set of
times has probability `∑_b p_b P(∑_{k=b+1}^{n} H_k ∈ A)`. -/
theorem map_connectionTime_apply {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) {A : Set ℝ}
    (hA : MeasurableSet A) :
    (trajectoryClockLaw n).map (connectionTime s) A
      = ∑ b ∈ Icc 1 n, stoppingLaw s b
          * ∫⁻ ω, A.indicator 1 (∑ j ∈ Ico (b - 1) (n - 1), ω j) ∂kingmanClock := by
  have hpt : ∀ p : List (ER n) × (ℕ → ℝ), (connectionTime s ⁻¹' A).indicator 1 p
      = A.indicator (1 : ℝ → ℝ≥0∞) (∑ j ∈ Ico (stoppingLevel s p.1 - 1) (n - 1), p.2 j) := by
    intro p
    by_cases hp : connectionTime s p ∈ A
    · have hp' : ∑ j ∈ Ico (stoppingLevel s p.1 - 1) (n - 1), p.2 j ∈ A := hp
      simp [hp, hp']
    · have hp' : ∑ j ∈ Ico (stoppingLevel s p.1 - 1) (n - 1), p.2 j ∉ A := hp
      simp [hp, hp']
  rw [Measure.map_apply (measurable_connectionTime s) hA,
    ← lintegral_indicator_one (measurable_connectionTime s hA), lintegral_congr hpt]
  exact lintegral_trajectoryClockLaw hn s
    (fun b ω ↦ A.indicator 1 (∑ j ∈ Ico (b - 1) (n - 1), ω j))
    fun b ↦ (measurable_one.indicator hA).comp
      (Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j)

/-- **The law of `τ_q` is equivalent to the connectivity cumulant.** For two interfaces on
`n ≥ 2` individuals, the connection times have the same law under the path law exactly when the
two cumulants are equal polynomials. -/
theorem map_connectionTime_eq_iff_connectivityCumulant_eq {n : ℕ} (hn : 2 ≤ n)
    (s s' : Fin n → Fin n) :
    (trajectoryClockLaw n).map (connectionTime s) = (trajectoryClockLaw n).map (connectionTime s')
      ↔ connectivityCumulant (Finpartition.ofSetoid (graphKer s))
        = connectivityCumulant (Finpartition.ofSetoid (graphKer s')) := by
  rw [← laplace_eq_iff_connectivityCumulant_eq hn s s']
  constructor
  · intro h θ hθ
    have hf : Measurable fun x : ℝ ↦ ENNReal.ofReal (Real.exp (-(θ * x))) :=
      (measurable_const.mul measurable_id').neg.exp.ennreal_ofReal
    calc ∫⁻ p, ENNReal.ofReal (Real.exp (-(θ * connectionTime s p))) ∂(trajectoryClockLaw n)
        = ∫⁻ x, ENNReal.ofReal (Real.exp (-(θ * x)))
            ∂((trajectoryClockLaw n).map (connectionTime s)) :=
          (lintegral_map hf (measurable_connectionTime s)).symm
      _ = ∫⁻ x, ENNReal.ofReal (Real.exp (-(θ * x)))
            ∂((trajectoryClockLaw n).map (connectionTime s')) := by rw [h]
      _ = ∫⁻ p, ENNReal.ofReal (Real.exp (-(θ * connectionTime s' p)))
            ∂(trajectoryClockLaw n) :=
          lintegral_map hf (measurable_connectionTime s')
  · intro h
    have hp := stoppingProb_eq_of_laplace_eq hn h
    refine Measure.ext fun A hA ↦ ?_
    rw [map_connectionTime_apply hn s hA, map_connectionTime_apply hn s' hA]
    refine sum_congr rfl fun b _ ↦ ?_
    rw [(ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp (hp b)]

/-! ### Kingman's exponentials and the spectral coefficients -/

/-- **Kingman's exponentials are linearly independent on `c ≥ 0`.** If
`∑_{k=2}^{n} a_k e^{-d_k c}` vanishes for every `c ≥ 0`, every `a_k` is zero. -/
theorem eq_zero_of_sum_mul_exp_deathRate {n : ℕ} {a : ℕ → ℝ}
    (h : ∀ c : ℝ, 0 ≤ c → ∑ k ∈ Ioc 1 n, a k * Real.exp (-(deathRate k * c)) = 0) :
    ∀ k ∈ Ioc 1 n, a k = 0 := by
  have hpow : ∀ (k : ℕ) (y : ℝ), 0 < y →
      Real.exp (-(deathRate k * -Real.log y)) = y ^ (k.choose 2) := by
    intro k y hy
    have hexp : -(deathRate k * -Real.log y) = ((k.choose 2 : ℕ) : ℝ) * Real.log y := by
      rw [ReportedConnectionLadder.deathRate_eq_choose_two]
      ring
    rw [hexp, Real.exp_nat_mul, Real.exp_log hy]
  have heval : ∀ y : ℝ, (∑ k ∈ Ioc 1 n, Polynomial.C (a k) * Polynomial.X ^ (k.choose 2)).eval y
      = ∑ k ∈ Ioc 1 n, a k * y ^ (k.choose 2) := by
    intro y
    simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
  have hzero : (∑ k ∈ Ioc 1 n, Polynomial.C (a k) * Polynomial.X ^ (k.choose 2)) = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _
      (Set.Infinite.mono ?_ (Set.Ioc_infinite (show (0 : ℝ) < 1 by norm_num)))
    intro y hy
    obtain ⟨hy0, hy1⟩ := hy
    have hc : 0 ≤ -Real.log y := neg_nonneg.mpr (Real.log_nonpos hy0.le hy1)
    have hroot : ∑ k ∈ Ioc 1 n, a k * y ^ (k.choose 2) = 0 := by
      refine (sum_congr rfl fun k _ ↦ ?_).trans (h (-Real.log y) hc)
      rw [hpow k y hy0]
    exact (heval y).trans hroot
  intro m hm
  have hcoeff := congrArg (fun P : Polynomial ℝ ↦ P.coeff (m.choose 2)) hzero
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at hcoeff
  rw [sum_eq_single m] at hcoeff
  · simpa using hcoeff
  · intro k hk hne
    refine if_neg fun heq ↦ hne ?_
    have hk1 := (mem_Ioc.mp hk).1
    have hm1 := (mem_Ioc.mp hm).1
    have hcast : deathRate m = deathRate k := by
      rw [ReportedConnectionLadder.deathRate_eq_choose_two m,
        ReportedConnectionLadder.deathRate_eq_choose_two k, heq]
    rcases lt_trichotomy k m with hlt | heq' | hgt
    · exact absurd hcast (deathRate_lt_deathRate (by omega) hlt).ne'
    · exact heq'
    · exact absurd hcast (deathRate_lt_deathRate (by omega) hgt).ne
  · intro hnot
    exact absurd hm hnot

/-- **The survival function of the first-step law carries exactly its spectral coefficients.**
Two interfaces on `n` individuals have the same survival function `P(τ_q > c)`, `c ≥ 0`, exactly
when their spectral coefficients `spectralCoeff s ⊥ k`, `k = 2, …, n`, agree. -/
theorem spectralCoeff_eq_iff_survivalAt_eq {n : ℕ} (s s' : Fin n → Fin n) :
    (∀ c : ℝ, 0 ≤ c →
      survivalAt (connectionTimeLaw s ⊥) c = survivalAt (connectionTimeLaw s' ⊥) c)
      ↔ ∀ k ∈ Ioc 1 n, spectralCoeff s ⊥ k = spectralCoeff s' ⊥ k := by
  constructor
  · intro h
    have hreal : ∀ c : ℝ, 0 ≤ c →
        ∑ k ∈ Ioc 1 n, (spectralCoeff s ⊥ k - spectralCoeff s' ⊥ k)
          * Real.exp (-(deathRate k * c)) = 0 := by
      intro c hc
      have h1 := survivalAt_connectionTimeLaw_toReal s ⊥ c hc
      have h2 := survivalAt_connectionTimeLaw_toReal s' ⊥ c hc
      rw [blocks_bot] at h1 h2
      rw [h c hc] at h1
      have heq : ∑ k ∈ Ioc 1 n, spectralCoeff s ⊥ k * Real.exp (-(deathRate k * c))
          = ∑ k ∈ Ioc 1 n, spectralCoeff s' ⊥ k * Real.exp (-(deathRate k * c)) :=
        h1.symm.trans h2
      rw [← sub_eq_zero, ← sum_sub_distrib] at heq
      refine (sum_congr rfl fun k _ ↦ ?_).trans heq
      ring
    exact fun k hk ↦ sub_eq_zero.mp
      (eq_zero_of_sum_mul_exp_deathRate
        (a := fun k ↦ spectralCoeff s ⊥ k - spectralCoeff s' ⊥ k) hreal k hk)
  · intro h c hc
    rw [survivalAt_connectionTimeLaw_bot s hc, survivalAt_connectionTimeLaw_bot s' hc]
    congr 1
    exact sum_congr rfl fun k hk ↦ by rw [h k hk]

/-! ### The first-step transform is (D7) -/

/-- A connected report has transform `1`. -/
theorem connectionLaplace_of_observed_eq_top {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n) (t : ℝ)
    {ξ : ER n} (hc : observed s ξ = ⊤) : connectionLaplace s t ξ = 1 := by
  have h := connectionValue_eq s t 1 0 ξ
  rw [if_pos ((blocks_observed_le_one_iff hn s ξ).mpr hc)] at h
  exact h

/-- **The backward equation's average over covers is the jump kernel**, for the transform: on an
unconnected report with `K` blocks, `E_ξ e^{-t τ_q} = d_K/(d_K + t) ∑_η J(ξ, η) E_η e^{-t τ_q}`. -/
theorem connectionLaplace_eq_sum_jumpLaw {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n) {t : ℝ}
    {ξ : ER n} (hk : 2 ≤ blocks ξ) (hc : observed s ξ ≠ ⊤) :
    connectionLaplace s t ξ = deathRate (blocks ξ) / (deathRate (blocks ξ) + t)
      * ∑ η : ER n, (jumpLaw ξ η).toReal * connectionLaplace s t η := by
  have hd := deathRate_pos hk
  have hsum : ∑ η : ER n, (jumpLaw ξ η).toReal * connectionLaplace s t η
      = (∑ η : {η : ER n // Covers ξ η}, connectionLaplace s t η.1) / deathRate (blocks ξ) := by
    simp only [jumpLaw_toReal hk, ite_mul, zero_mul]
    rw [← sum_filter, sum_div]
    refine sum_bij' (fun η h ↦ ⟨η, (mem_filter.mp h).2⟩) (fun η _ ↦ η.1)
      (fun _ _ ↦ mem_univ _) (fun η _ ↦ mem_filter.mpr ⟨mem_univ _, η.2⟩) (fun _ _ ↦ rfl)
      (fun _ _ ↦ rfl) fun η _ ↦ ?_
    ring
  have hrec := connectionValue_eq s t 1 0 ξ
  rw [if_neg fun h ↦ hc ((blocks_observed_le_one_iff hn s ξ).mp h)] at hrec
  have hrec' : connectionLaplace s t ξ
      = (∑ η : {η : ER n // Covers ξ η}, connectionLaplace s t η.1)
        / (deathRate (blocks ξ) + t) := by
    simpa only [Pi.zero_apply, zero_add] using hrec
  rw [hsum, hrec', div_mul_div_comm, mul_comm (deathRate (blocks ξ)),
    mul_div_mul_right _ _ hd.ne']

/-- **One level of the first-step transform.** Averaged over the head law at `b + 1` blocks,
the unconnected states' transforms are `d_{b+1}/(d_{b+1} + t)` times the probability of first
connecting at `b` plus the unconnected average at `b` blocks. -/
theorem sum_blockLaw_connectionLaplace_succ {n b : ℕ} (s : Fin n → Fin n) {t : ℝ} (hb : 1 ≤ b)
    (hbn : b + 1 ≤ n) :
    ∑ ξ : ER n, (blockLaw n (n - (b + 1)) ξ).toReal
        * (if observed s ξ = ⊤ then 0 else connectionLaplace s t ξ)
      = deathRate (b + 1) / (deathRate (b + 1) + t)
        * (firstConnectionProbability s b
          + ∑ η : ER n, (blockLaw n (n - b) η).toReal
              * (if observed s η = ⊤ then 0 else connectionLaplace s t η)) := by
  have hn : 0 < n := by omega
  have hlevel : ∀ ξ : ER n, (blockLaw n (n - (b + 1)) ξ).toReal
        * (if observed s ξ = ⊤ then 0 else connectionLaplace s t ξ)
      = deathRate (b + 1) / (deathRate (b + 1) + t)
        * ∑ η : ER n, ((blockLaw n (n - (b + 1)) ξ).toReal * (jumpLaw ξ η).toReal
            * (if observed s ξ ≠ ⊤ ∧ observed s η = ⊤ then 1 else 0)
          + (blockLaw n (n - (b + 1)) ξ).toReal * (jumpLaw ξ η).toReal
            * (if observed s η = ⊤ then 0 else connectionLaplace s t η)) := by
    intro ξ
    by_cases hξ : blocks ξ = b + 1
    · by_cases hc : observed s ξ = ⊤
      · rw [if_pos hc, mul_zero]
        refine (mul_eq_zero_of_right _ (sum_eq_zero fun η _ ↦ ?_)).symm
        by_cases hJ : (jumpLaw ξ η).toReal = 0
        · rw [hJ]
          ring
        · have hle : ξ ≤ η := le_of_mem_support_jumpLaw
            ((PMF.mem_support_iff _ _).mpr fun hzero ↦ hJ (by rw [hzero, ENNReal.toReal_zero]))
          have hη : observed s η = ⊤ := top_unique (hc.symm.le.trans (observed_mono s hle))
          rw [if_neg (show ¬(observed s ξ ≠ ⊤ ∧ observed s η = ⊤) from fun h ↦ h.1 hc),
            if_pos hη]
          ring
      · rw [if_neg hc, connectionLaplace_eq_sum_jumpLaw hn s (by omega) hc, hξ,
          mul_left_comm, mul_sum]
        congr 1
        refine sum_congr rfl fun η _ ↦ ?_
        by_cases hη : observed s η = ⊤
        · rw [if_pos (show observed s ξ ≠ ⊤ ∧ observed s η = ⊤ from ⟨hc, hη⟩), if_pos hη,
            connectionLaplace_of_observed_eq_top hn s t hη]
          ring
        · rw [if_neg (show ¬(observed s ξ ≠ ⊤ ∧ observed s η = ⊤) from fun h ↦ hη h.2),
            if_neg hη]
          ring
    · have hzero : (blockLaw n (n - (b + 1)) ξ).toReal = 0 := by
        rw [blockLaw_toReal (n - (b + 1)) (by omega) ξ,
          if_neg (show ¬blocks ξ = n - (n - (b + 1)) by omega)]
      simp only [hzero, zero_mul, add_zero, sum_const_zero, mul_zero]
  rw [sum_congr rfl fun ξ _ ↦ hlevel ξ, ← mul_sum]
  congr 1
  simp only [sum_add_distrib]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun η _ ↦ ?_
  rw [← sum_mul, ← blockLaw_succ_toReal, show n - (b + 1) + 1 = n - b by omega]

/-- **The first-step transform at `⊥` is (D7).** For every real `t`, the solution of the backward
equation `connectionLaplace s t ⊥` is `∑_b p_b ∏_{k=b+1}^{n} d_k/(d_k + t)`. -/
theorem connectionLaplace_bot_eq_sum_stoppingProb {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n)
    {t : ℝ} :
    connectionLaplace s t ⊥
      = ∑ b ∈ Icc 1 n, stoppingProb s b * ∏ k ∈ Ioc b n, deathRate k / (deathRate k + t) := by
  have hn0 : 0 < n := by omega
  have hlaw : blockLaw n (n - n) = PMF.pure (Delta n) := by
    rw [Nat.sub_self, blockLaw_eq_map, chainLaw, PMF.pure_map]
    rfl
  have hsingle : ∑ ξ : ER n, (blockLaw n (n - n) ξ).toReal
      * (if observed s ξ = ⊤ then 0 else connectionLaplace s t ξ)
      = if observed s (Delta n) = ⊤ then 0 else connectionLaplace s t (Delta n) := by
    rw [hlaw, sum_eq_single (Delta n)]
    · simp [PMF.pure_apply]
    · intro ξ _ hne
      simp [PMF.pure_apply, hne]
    · intro hmem
      exact absurd (mem_univ _) hmem
  have hFn : stoppingProb s n = if observed s (Delta n) = ⊤ then 1 else 0 := by
    rw [stoppingProb_self (by omega) s]
    unfold connectedProb
    rw [hlaw, sum_filter, sum_eq_single (Delta n)]
    · by_cases hc : observed s (Delta n) = ⊤ <;> simp [hc, PMF.pure_apply]
    · intro ξ _ hne
      simp [PMF.pure_apply, hne]
    · intro hmem
      exact absurd (mem_univ _) hmem
  have htop : ∑ i ∈ Icc n n, stoppingProb s i * ∏ k ∈ Ioc i n, deathRate k / (deathRate k + t)
      + (∏ k ∈ Ioc n n, deathRate k / (deathRate k + t))
        * ∑ ξ : ER n, (blockLaw n (n - n) ξ).toReal
            * (if observed s ξ = ⊤ then 0 else connectionLaplace s t ξ)
      = connectionLaplace s t ⊥ := by
    rw [Icc_self, sum_singleton, Ioc_self, prod_empty, mul_one, one_mul, hsingle, hFn]
    by_cases hc : observed s (Delta n) = ⊤
    · rw [if_pos hc, if_pos hc, add_zero, connectionLaplace_of_observed_eq_top hn0 s t hc]
    · rw [if_neg hc, if_neg hc, zero_add]
  have hstep : ∀ b, 1 ≤ b → b + 1 ≤ n →
      ∑ i ∈ Icc (b + 1) n, stoppingProb s i * ∏ k ∈ Ioc i n, deathRate k / (deathRate k + t)
        + (∏ k ∈ Ioc (b + 1) n, deathRate k / (deathRate k + t))
          * ∑ ξ : ER n, (blockLaw n (n - (b + 1)) ξ).toReal
              * (if observed s ξ = ⊤ then 0 else connectionLaplace s t ξ)
      = ∑ i ∈ Icc b n, stoppingProb s i * ∏ k ∈ Ioc i n, deathRate k / (deathRate k + t)
        + (∏ k ∈ Ioc b n, deathRate k / (deathRate k + t))
          * ∑ η : ER n, (blockLaw n (n - b) η).toReal
              * (if observed s η = ⊤ then 0 else connectionLaplace s t η) := by
    intro b hb hbn
    have hsplit : ∑ i ∈ Icc b n, stoppingProb s i * ∏ k ∈ Ioc i n, deathRate k / (deathRate k + t)
        = ∑ i ∈ Icc (b + 1) n, stoppingProb s i * ∏ k ∈ Ioc i n, deathRate k / (deathRate k + t)
          + stoppingProb s b * ∏ k ∈ Ioc b n, deathRate k / (deathRate k + t) := by
      rw [sum_eq_sum_diff_singleton_add (mem_Icc.mpr ⟨le_rfl, by omega⟩)]
      congr 2
      ext x
      simp only [mem_sdiff, mem_Icc, mem_singleton]
      omega
    have hprod : ∏ k ∈ Ioc b n, deathRate k / (deathRate k + t)
        = (∏ k ∈ Ioc (b + 1) n, deathRate k / (deathRate k + t))
          * (deathRate (b + 1) / (deathRate (b + 1) + t)) := by
      rw [prod_eq_prod_diff_singleton_mul (mem_Ioc.mpr ⟨by omega, hbn⟩)]
      congr 2
      ext x
      simp only [mem_sdiff, mem_Ioc, mem_singleton]
      omega
    rw [sum_blockLaw_connectionLaplace_succ s hb hbn,
      ← stoppingProb_eq_firstConnectionProbability s hb (by omega), hsplit, hprod]
    ring
  have hbottom : ∑ ξ : ER n, (blockLaw n (n - 1) ξ).toReal
      * (if observed s ξ = ⊤ then 0 else connectionLaplace s t ξ) = 0 := by
    refine sum_eq_zero fun ξ _ ↦ ?_
    by_cases hb : blocks ξ = 1
    · have hconn : observed s ξ = ⊤ := by
        haveI : NeZero n := ⟨by omega⟩
        rw [(blocks_eq_one_iff ξ).mp hb]
        exact top_sup_eq _
      rw [if_pos hconn, mul_zero]
    · rw [blockLaw_toReal (n - 1) (by omega) ξ,
        if_neg (show ¬blocks ξ = n - (n - 1) by omega), zero_mul]
  have hall : ∀ i b, b + i = n → 1 ≤ b →
      ∑ j ∈ Icc b n, stoppingProb s j * ∏ k ∈ Ioc j n, deathRate k / (deathRate k + t)
        + (∏ k ∈ Ioc b n, deathRate k / (deathRate k + t))
          * ∑ ξ : ER n, (blockLaw n (n - b) ξ).toReal
              * (if observed s ξ = ⊤ then 0 else connectionLaplace s t ξ)
      = connectionLaplace s t ⊥ := by
    intro i
    induction i with
    | zero =>
      intro b hbi _
      obtain rfl : b = n := by omega
      exact htop
    | succ i ih =>
      intro b hbi hb
      rw [← hstep b hb (by omega)]
      exact ih (b + 1) (by omega) (by omega)
  have h1 := hall (n - 1) 1 (by omega) le_rfl
  rw [hbottom, mul_zero, add_zero] at h1
  exact h1.symm

/-- **The first-step law and the path law have the same Laplace transform.** At every `t ≥ 0`,
`∫ e^{-t x} d(connectionTimeLaw s ⊥)` is the path expectation `E e^{-t τ_q}`. -/
theorem lintegral_exp_connectionTimeLaw_bot_eq_laplace {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-(t * (x : ℝ)))) ∂(connectionTimeLaw s ⊥)
      = ∫⁻ p, ENNReal.ofReal (Real.exp (-(t * connectionTime s p))) ∂(trajectoryClockLaw n) := by
  rw [lintegral_exp_connectionTimeLaw s ht ⊥, connectionTime_laplace hn s ht,
    connectionLaplace_bot_eq_sum_stoppingProb hn s]

/-- A survival function on `[0, ∞)` determines the first-step law. -/
theorem connectionTimeLaw_bot_eq_of_survivalAt_eq {n : ℕ} {s s' : Fin n → Fin n}
    (h : ∀ c : ℝ, 0 ≤ c →
      survivalAt (connectionTimeLaw s ⊥) c = survivalAt (connectionTimeLaw s' ⊥) c) :
    connectionTimeLaw s ⊥ = connectionTimeLaw s' ⊥ := by
  haveI := connectionTimeLaw_isProbabilityMeasure s ⊥
  haveI := connectionTimeLaw_isProbabilityMeasure s' ⊥
  refine Measure.ext_of_Iic _ _ fun a ↦ ?_
  have hset : {y : ℝ≥0 | (a : ℝ) < (y : ℝ)} = (Set.Iic a)ᶜ := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_Iic, not_le, NNReal.coe_lt_coe]
  have ha := h a a.coe_nonneg
  unfold survivalAt at ha
  rw [hset] at ha
  rw [← compl_compl (Set.Iic a), prob_compl_eq_one_sub measurableSet_Iic.compl,
    prob_compl_eq_one_sub measurableSet_Iic.compl, ha]

/-- **Equal survival functions of the first-step law force equal cumulants.** -/
theorem connectivityCumulant_eq_of_survivalAt_eq {n : ℕ} (hn : 2 ≤ n) {s s' : Fin n → Fin n}
    (h : ∀ c : ℝ, 0 ≤ c →
      survivalAt (connectionTimeLaw s ⊥) c = survivalAt (connectionTimeLaw s' ⊥) c) :
    connectivityCumulant (Finpartition.ofSetoid (graphKer s))
      = connectivityCumulant (Finpartition.ofSetoid (graphKer s')) := by
  have hlaw := connectionTimeLaw_bot_eq_of_survivalAt_eq h
  refine (laplace_eq_iff_connectivityCumulant_eq hn s s').mp fun θ hθ ↦ ?_
  rw [← lintegral_exp_connectionTimeLaw_bot_eq_laplace hn s hθ,
    ← lintegral_exp_connectionTimeLaw_bot_eq_laplace hn s' hθ, hlaw]

/-- **Equal spectral coefficients force equal cumulants.** -/
theorem connectivityCumulant_eq_of_spectralCoeff_eq {n : ℕ} (hn : 2 ≤ n) {s s' : Fin n → Fin n}
    (h : ∀ k ∈ Ioc 1 n, spectralCoeff s ⊥ k = spectralCoeff s' ⊥ k) :
    connectivityCumulant (Finpartition.ofSetoid (graphKer s))
      = connectivityCumulant (Finpartition.ofSetoid (graphKer s')) :=
  connectivityCumulant_eq_of_survivalAt_eq hn ((spectralCoeff_eq_iff_survivalAt_eq s s').mpr h)

/-! ### The cumulant gives back the spectral coefficients -/

/-- **The first-step transform in spectral form.** For `t ≥ 0`, from every state,
`E_ξ e^{-t τ_q} = 1 - ∑_{k=2}^{K} spectralCoeff s ξ k · t/(t + d_k)` with `K = blocks ξ`. -/
theorem connectionLaplace_eq_one_sub_sum_spectralCoeff {n : ℕ} (s : Fin n → Fin n) {t : ℝ}
    (ht : 0 ≤ t) (ξ : ER n) :
    connectionLaplace s t ξ
      = 1 - ∑ k ∈ Ioc 1 (blocks ξ), spectralCoeff s ξ k * (t / (t + deathRate k)) := by
  induction ξ using covers_induction with
  | step ξ ih =>
    by_cases hr : blocks (observed s ξ) ≤ 1
    · have hV := connectionValue_eq s t 1 0 ξ
      rw [if_pos hr] at hV
      have hvanish : ∀ k ∈ Ioc 1 (blocks ξ),
          spectralCoeff s ξ k * (t / (t + deathRate k)) = 0 :=
        fun k _ ↦ by rw [spectralCoeff_eq, if_pos hr, zero_mul]
      rw [sum_eq_zero hvanish, sub_zero]
      exact hV
    · have hk := two_le_blocks_of_not_le_one s hr
      have hd := deathRate_pos hk
      have hdt : 0 < deathRate (blocks ξ) + t := by linarith
      have hrec := connectionValue_eq s t 1 0 ξ
      rw [if_neg hr] at hrec
      have hV : connectionLaplace s t ξ
          = (∑ η : {η : ER n // Covers ξ η}, connectionLaplace s t η.1)
            / (deathRate (blocks ξ) + t) := by
        simpa only [Pi.zero_apply, zero_add] using hrec
      have hrow : ∀ η : {η : ER n // Covers ξ η}, connectionLaplace s t η.1
          = 1 - ∑ j ∈ Ioc 1 (blocks ξ - 1),
            spectralCoeff s η.1 j * (t / (t + deathRate j)) := by
        intro η
        have hη : blocks η.1 = blocks ξ - 1 := by
          have := η.2.2
          omega
        rw [ih η.1 η.2, hη]
      have hcard : (∑ _η : {η : ER n // Covers ξ η}, (1 : ℝ)) = deathRate (blocks ξ) := by
        rw [sum_const, nsmul_eq_mul, card_univ, ← Nat.card_eq_fintype_card,
          card_covers_eq_deathRate, mul_one]
      have hsum : ∑ η : {η : ER n // Covers ξ η}, connectionLaplace s t η.1
          = deathRate (blocks ξ)
            - ∑ j ∈ Ioc 1 (blocks ξ - 1),
                (∑ η : {η : ER n // Covers ξ η}, spectralCoeff s η.1 j)
                  * (t / (t + deathRate j)) := by
        rw [sum_congr rfl fun η _ ↦ hrow η, sum_sub_distrib, hcard, sum_comm]
        congr 1
        exact sum_congr rfl fun j _ ↦ (sum_mul _ _ _).symm
      have hsplitTop : ∑ k ∈ Ioc 1 (blocks ξ), spectralCoeff s ξ k * (t / (t + deathRate k))
          = ∑ k ∈ Ioc 1 (blocks ξ - 1), spectralCoeff s ξ k * (t / (t + deathRate k))
            + spectralCoeff s ξ (blocks ξ) * (t / (t + deathRate (blocks ξ))) := by
        have h := sum_Ioc_succ_top (show 1 ≤ blocks ξ - 1 by omega)
          (fun k ↦ spectralCoeff s ξ k * (t / (t + deathRate k)))
        rwa [Nat.sub_add_cancel (show 1 ≤ blocks ξ by omega)] at h
      have hlow : ∀ k ∈ Ioc 1 (blocks ξ - 1), spectralCoeff s ξ k * (t / (t + deathRate k))
          = deathRate (blocks ξ) / (deathRate (blocks ξ) - deathRate k) * coverAverage s ξ k
            * (t / (t + deathRate k)) := by
        intro k hk'
        have hkK : k < blocks ξ := by
          have := (mem_Ioc.mp hk').2
          omega
        rw [spectralCoeff_eq, if_neg hr, if_pos hkK]
      have htop : spectralCoeff s ξ (blocks ξ)
          = 1 - ∑ j ∈ Ioc 1 (blocks ξ - 1),
            deathRate (blocks ξ) / (deathRate (blocks ξ) - deathRate j) * coverAverage s ξ j := by
        rw [spectralCoeff_eq, if_neg hr, if_neg (lt_irrefl _), if_pos rfl]
      have hpiece : ∀ j ∈ Ioc 1 (blocks ξ - 1),
          (∑ η : {η : ER n // Covers ξ η}, spectralCoeff s η.1 j) * (t / (t + deathRate j))
              / (deathRate (blocks ξ) + t)
            = deathRate (blocks ξ) / (deathRate (blocks ξ) - deathRate j) * coverAverage s ξ j
              * (t / (t + deathRate j) - t / (t + deathRate (blocks ξ))) := by
        intro j hj
        have hj2 : 2 ≤ j := by
          have := (mem_Ioc.mp hj).1
          omega
        have hjK : j < blocks ξ := by
          have := (mem_Ioc.mp hj).2
          omega
        have hdj := deathRate_pos hj2
        have hgap : deathRate (blocks ξ) - deathRate j ≠ 0 :=
          (sub_pos.mpr (deathRate_lt_deathRate (by omega) hjK)).ne'
        have htj : t + deathRate j ≠ 0 := (show 0 < t + deathRate j by linarith).ne'
        have htK : t + deathRate (blocks ξ) ≠ 0 :=
          (show 0 < t + deathRate (blocks ξ) by linarith).ne'
        rw [coverAverage]
        field_simp
        ring
      have hA : ∑ j ∈ Ioc 1 (blocks ξ - 1),
            deathRate (blocks ξ) / (deathRate (blocks ξ) - deathRate j) * coverAverage s ξ j
              * (t / (t + deathRate j) - t / (t + deathRate (blocks ξ)))
          = ∑ j ∈ Ioc 1 (blocks ξ - 1),
              deathRate (blocks ξ) / (deathRate (blocks ξ) - deathRate j) * coverAverage s ξ j
                * (t / (t + deathRate j))
            - (∑ j ∈ Ioc 1 (blocks ξ - 1),
                deathRate (blocks ξ) / (deathRate (blocks ξ) - deathRate j) * coverAverage s ξ j)
              * (t / (t + deathRate (blocks ξ))) := by
        rw [sum_mul, ← sum_sub_distrib]
        exact sum_congr rfl fun j _ ↦ by ring
      have hτ : 1 - t / (t + deathRate (blocks ξ))
          = deathRate (blocks ξ) / (deathRate (blocks ξ) + t) := by
        have htK : t + deathRate (blocks ξ) ≠ 0 :=
          (show 0 < t + deathRate (blocks ξ) by linarith).ne'
        field_simp
        ring
      rw [hV, hsum, sub_div, sum_div, sum_congr rfl hpiece, hA, hsplitTop, sum_congr rfl hlow,
        htop, ← hτ]
      ring

/-- **The partial fractions `t/(t + d_k)` are linearly independent.** If
`∑_{k=2}^{n} a_k t/(t + d_k)` vanishes for every `t ≥ 0`, every `a_k` is zero. -/
theorem eq_zero_of_sum_mul_div_add_deathRate {n : ℕ} {a : ℕ → ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → ∑ k ∈ Ioc 1 n, a k * (t / (t + deathRate k)) = 0) :
    ∀ k ∈ Ioc 1 n, a k = 0 := by
  have hclear : ∀ t : ℝ, 0 < t →
      ∑ k ∈ Ioc 1 n, a k * ∏ j ∈ (Ioc 1 n).erase k, (t + deathRate j) = 0 := by
    intro t htpos
    have hpos : ∀ j ∈ Ioc 1 n, 0 < t + deathRate j := fun j hj ↦
      add_pos htpos (deathRate_pos (by have := (mem_Ioc.mp hj).1; omega))
    have hterm : ∀ k ∈ Ioc 1 n,
        a k * (t / (t + deathRate k)) * ∏ j ∈ Ioc 1 n, (t + deathRate j)
          = t * (a k * ∏ j ∈ (Ioc 1 n).erase k, (t + deathRate j)) := by
      intro k hk
      have hc : t / (t + deathRate k) * (t + deathRate k) = t :=
        div_mul_cancel₀ t (hpos k hk).ne'
      rw [← mul_prod_erase _ _ hk]
      calc a k * (t / (t + deathRate k))
            * ((t + deathRate k) * ∏ j ∈ (Ioc 1 n).erase k, (t + deathRate j))
          = a k * (∏ j ∈ (Ioc 1 n).erase k, (t + deathRate j))
              * (t / (t + deathRate k) * (t + deathRate k)) := by ring
        _ = t * (a k * ∏ j ∈ (Ioc 1 n).erase k, (t + deathRate j)) := by
            rw [hc]
            ring
    have hmul : t * ∑ k ∈ Ioc 1 n, a k * ∏ j ∈ (Ioc 1 n).erase k, (t + deathRate j) = 0 := by
      rw [mul_sum, ← sum_congr rfl hterm, ← sum_mul, h t htpos.le, zero_mul]
    exact (mul_eq_zero.mp hmul).resolve_left htpos.ne'
  have heval : ∀ t : ℝ, (∑ k ∈ Ioc 1 n, Polynomial.C (a k)
        * ∏ j ∈ (Ioc 1 n).erase k, (Polynomial.X + Polynomial.C (deathRate j))).eval t
      = ∑ k ∈ Ioc 1 n, a k * ∏ j ∈ (Ioc 1 n).erase k, (t + deathRate j) := by
    intro t
    simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X]
  have hzero : (∑ k ∈ Ioc 1 n, Polynomial.C (a k)
      * ∏ j ∈ (Ioc 1 n).erase k, (Polynomial.X + Polynomial.C (deathRate j))) = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _
      (Set.Infinite.mono ?_ (Set.Ioi_infinite (0 : ℝ)))
    intro t ht
    exact (heval t).trans (hclear t ht)
  intro m hm
  have hev := heval (-deathRate m)
  rw [hzero, Polynomial.eval_zero, sum_eq_single m] at hev
  · have hP : ∏ j ∈ (Ioc 1 n).erase m, (-deathRate m + deathRate j) ≠ 0 := by
      refine prod_ne_zero_iff.mpr fun j hj ↦ ?_
      obtain ⟨hjm, hj'⟩ := mem_erase.mp hj
      have hj1 := (mem_Ioc.mp hj').1
      have hm1 := (mem_Ioc.mp hm).1
      rcases lt_or_gt_of_ne hjm with hlt | hgt
      · have := deathRate_lt_deathRate (show 1 ≤ j by omega) hlt
        exact (show -deathRate m + deathRate j < 0 by linarith).ne
      · have := deathRate_lt_deathRate (show 1 ≤ m by omega) hgt
        exact (show 0 < -deathRate m + deathRate j by linarith).ne'
    exact (mul_eq_zero.mp hev.symm).resolve_right hP
  · intro k _ hne
    have hvanish : ∏ j ∈ (Ioc 1 n).erase k, (-deathRate m + deathRate j) = 0 :=
      prod_eq_zero (show m ∈ (Ioc 1 n).erase k from mem_erase.mpr ⟨fun h ↦ hne h.symm, hm⟩)
        (show -deathRate m + deathRate m = 0 by ring)
    rw [hvanish, mul_zero]
  · intro hnot
    exact absurd hm hnot

/-- **The cumulant determines the spectral coefficients.** -/
theorem spectralCoeff_eq_of_connectivityCumulant_eq {n : ℕ} (hn : 2 ≤ n) {s s' : Fin n → Fin n}
    (h : connectivityCumulant (Finpartition.ofSetoid (graphKer s))
      = connectivityCumulant (Finpartition.ofSetoid (graphKer s'))) :
    ∀ k ∈ Ioc 1 n, spectralCoeff s ⊥ k = spectralCoeff s' ⊥ k := by
  have hp := stoppingProb_eq_of_connectedProb_eq hn (connectedProb_eq_of_connectivityCumulant_eq h)
  have hreal : ∀ t : ℝ, 0 ≤ t →
      ∑ k ∈ Ioc 1 n, (spectralCoeff s ⊥ k - spectralCoeff s' ⊥ k) * (t / (t + deathRate k))
        = 0 := by
    intro t ht
    have h1 := connectionLaplace_eq_one_sub_sum_spectralCoeff s ht ⊥
    have h2 := connectionLaplace_eq_one_sub_sum_spectralCoeff s' ht ⊥
    rw [blocks_bot] at h1 h2
    have hlap : connectionLaplace s t ⊥ = connectionLaplace s' t ⊥ := by
      rw [connectionLaplace_bot_eq_sum_stoppingProb hn s,
        connectionLaplace_bot_eq_sum_stoppingProb hn s']
      simp only [hp]
    have heq : ∑ k ∈ Ioc 1 n, spectralCoeff s ⊥ k * (t / (t + deathRate k))
        = ∑ k ∈ Ioc 1 n, spectralCoeff s' ⊥ k * (t / (t + deathRate k)) := by
      linarith
    rw [← sub_eq_zero, ← sum_sub_distrib] at heq
    refine (sum_congr rfl fun k _ ↦ ?_).trans heq
    ring
  exact fun k hk ↦ sub_eq_zero.mp
    (eq_zero_of_sum_mul_div_add_deathRate
      (a := fun k ↦ spectralCoeff s ⊥ k - spectralCoeff s' ⊥ k) hreal k hk)

/-- **The spectral coefficients of the first-step law are equivalent to the cumulant.** -/
theorem spectralCoeff_eq_iff_connectivityCumulant_eq {n : ℕ} (hn : 2 ≤ n)
    (s s' : Fin n → Fin n) :
    (∀ k ∈ Ioc 1 n, spectralCoeff s ⊥ k = spectralCoeff s' ⊥ k)
      ↔ connectivityCumulant (Finpartition.ofSetoid (graphKer s))
        = connectivityCumulant (Finpartition.ofSetoid (graphKer s')) :=
  ⟨connectivityCumulant_eq_of_spectralCoeff_eq hn, spectralCoeff_eq_of_connectivityCumulant_eq hn⟩

/-- **The survival function of the first-step law is equivalent to the cumulant.** -/
theorem survivalAt_eq_iff_connectivityCumulant_eq {n : ℕ} (hn : 2 ≤ n) (s s' : Fin n → Fin n) :
    (∀ c : ℝ, 0 ≤ c →
      survivalAt (connectionTimeLaw s ⊥) c = survivalAt (connectionTimeLaw s' ⊥) c)
      ↔ connectivityCumulant (Finpartition.ofSetoid (graphKer s))
        = connectivityCumulant (Finpartition.ofSetoid (graphKer s')) := by
  rw [spectralCoeff_eq_iff_survivalAt_eq, spectralCoeff_eq_iff_connectivityCumulant_eq hn]

/-- **The first-step law is equivalent to the cumulant.** -/
theorem connectionTimeLaw_bot_eq_iff_connectivityCumulant_eq {n : ℕ} (hn : 2 ≤ n)
    (s s' : Fin n → Fin n) :
    connectionTimeLaw s ⊥ = connectionTimeLaw s' ⊥
      ↔ connectivityCumulant (Finpartition.ofSetoid (graphKer s))
        = connectivityCumulant (Finpartition.ofSetoid (graphKer s')) := by
  rw [← survivalAt_eq_iff_connectivityCumulant_eq hn]
  exact ⟨fun h c _ ↦ by rw [h], connectionTimeLaw_bot_eq_of_survivalAt_eq⟩

end Descent.Pangenome.GraphCoalescent.ConnectionLawIdentifiability
