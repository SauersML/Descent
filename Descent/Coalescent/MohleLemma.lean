/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.ExpRemainder
import Mathlib.Tactic

namespace Descent

/-!
# Möhle's lemma: two time scales, and what survives the fast one

Kingman's K-G (2.14), which `Descent.Coalescent.SemigroupLimit` proves and
`Descent.Coalescent.BlockMatrixLimit` instantiates, expands the one-generation operator as
`P_N = 1 + N⁻¹Q + O(N⁻²)`.  The leading term is the IDENTITY: nothing happens in a single
generation, and the coalescent is what `N` generations of almost-nothing accumulate to.

Many population models are not like that.  Diploidy, strong selfing, cyclical size change,
population subdivision with fast internal migration -- each has something that happens on
EVERY generation, and something else that happens on the order of `N` of them.  For those the
expansion is

  `P_N = A + N⁻¹B + O(N⁻²)`

with `A` a PROJECTION (`A² = A`) rather than the identity: `A` is what the fast dynamics
settles to, and `B` is the slow perturbation on top of it.  Möhle's lemma says what `N`
generations converge to, and the answer is not `exp B`:

  `P_N^N → A · exp(A B A)`.

## Why `ABA` and not `B`

The projection sandwiches the perturbation.  Only the part of `B` that maps the range of `A`
back into the range of `A` survives; everything else is erased on the fast time scale before
it can accumulate.  `mohle_limit` derives this rather than assuming it, and the derivation
makes the mechanism visible in three steps.

1.  **The off-range parts vanish in ONE step.**  `‖(1 - A)P_N‖ = ‖(1 - A)(A + E)‖ = ‖(1-A)E‖`,
    because `A - A² = 0`.  So `‖(1 - A)P_N^N‖ ≤ 2‖E‖ = O(N⁻¹)`, and likewise on the right.
    The `N`-generation operator is therefore `A P_N^N A` up to `O(N⁻¹)`: whatever the fast
    dynamics does to directions outside the projection's range, it does it immediately and
    once.
2.  **The sandwiched chain obeys a clean recursion.**  Writing `Yₙ = A P_N^n A`,
    `Y_{n+1} = Yₙ · D + εₙ` where `D = A exp(N⁻¹ABA)` and `‖εₙ‖ = O(N⁻²)`.  The error is
    `N⁻¹ · A P_N^n (1 - A) B A` plus genuine `O(N⁻²)` terms, and the first is `O(N⁻²)`
    because of step 1 -- it is `(1-A)` applied AFTER `n` generations, which by then is small.
    At `n = 0` it is exactly zero, since `A(1 - A) = 0`.
3.  **A recursion with `O(N⁻²)` defect run `N` times is `O(N⁻¹)` off.**
    `norm_sub_mul_pow_le` telescopes it, and `idem_mul_exp_pow` evaluates the comparison
    exactly: `(A exp(sG))^m = A exp(ms · G)`, so at `s = N⁻¹` and `m = N` it is `A exp(G)`
    on the nose, with no limit taken.

## What this is for

It is the last of the four gaps `Descent.Coalescent.Program` recorded around the convergence
theorems.  With `SemigroupLimit` for the `A = 1` case and this for general idempotent `A`,
the corpus covers both shapes a population-genetic transition operator comes in, and a model
with two time scales no longer has to posit its limit.

Kingman's coalescent is the case `A = 1`, where `ABA = B` and the lemma degenerates to
K-G (2.14).  That is the sense in which every one of these models is Kingman's up to a
time change: the projection is trivial exactly when nothing happens on the fast scale.

## Main results

- `idem_mul_exp_pow`: `(A exp(sG))^m = A exp(ms · G)` when `A` is idempotent and absorbs `G`.
- `norm_sub_mul_pow_le`: a recursion with defect `ε` is within `mεM` of its exact solution.
- `norm_one_sub_mul_pow_le`: **the off-range part dies in one generation**, which is the
  whole reason `ABA` appears in place of `B`.
- `mohle_limit`: **`P_N^N → A exp(ABA)`**, Möhle's lemma.
-/

namespace Coalescent

open NormedSpace Filter Topology

-- The recursion estimate carries large operator expressions through `nlinarith`; the
-- default budget is not enough to elaborate them.
set_option maxHeartbeats 2000000

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-! ### The comparison family -/

/-- **`A` commutes with anything it absorbs.**  If `A G = G A = G` then `A` commutes with
`s • G`, hence with its exponential. -/
theorem commute_idem_smul {A G : 𝔸} (hAG : A * G = G) (hGA : G * A = G) (s : ℝ) :
    Commute A (s • G) := by
  unfold Commute SemiconjBy
  rw [mul_smul_comm, smul_mul_assoc, hAG, hGA]

/-- **The comparison family's powers are exact.**  `(A exp(sG))^(m+1) = A exp((m+1)s · G)`:
the projection is idempotent and the exponentials add, so no error accumulates.

This is what makes the whole argument an estimate on a single recursion rather than a limit
of limits -- the object being compared against is evaluated in closed form. -/
theorem idem_mul_exp_pow {A G : 𝔸} (hA : A * A = A) (hAG : A * G = G) (hGA : G * A = G)
    (s : ℝ) (m : ℕ) :
    (A * exp ℝ (s • G)) ^ (m + 1) = A * exp ℝ (((m + 1 : ℕ) * s) • G) := by
  induction m with
  | zero => simp
  | succ p ih =>
    rw [pow_succ, ih]
    have hcommAll : ∀ r : ℝ, Commute A (exp ℝ (r • G)) := fun r ↦
      (commute_idem_smul hAG hGA r).exp_right ℝ
    have hstep : A * exp ℝ (((p + 1 : ℕ) * s) • G) * (A * exp ℝ (s • G))
        = A * A * (exp ℝ (((p + 1 : ℕ) * s) • G) * exp ℝ (s • G)) := by
      rw [mul_assoc, ← mul_assoc (exp ℝ (((p + 1 : ℕ) * s) • G)) A,
        ← (hcommAll ((p + 1 : ℕ) * s)).eq, mul_assoc, ← mul_assoc]
    rw [hstep, hA]
    congr 1
    rw [← exp_add_of_commute]
    · congr 1
      rw [← add_smul]
      congr 1
      push_cast
      ring
    · exact (Commute.refl G).smul_left _ |>.smul_right _

/-- **`N` steps of the comparison family at rate `N⁻¹` is exactly `A exp G`.**  No limit is
taken: the semigroup is evaluated in closed form, which is what leaves only the recursion's
defect to estimate. -/
theorem idem_mul_exp_pow_self {A G : 𝔸} (hA : A * A = A) (hAG : A * G = G) (hGA : G * A = G)
    {N : ℕ} (hN : 1 ≤ N) : (A * exp ℝ ((1 / (N : ℝ)) • G)) ^ N = A * exp ℝ G := by
  obtain ⟨q, rfl⟩ : ∃ q, N = q + 1 := ⟨N - 1, by omega⟩
  rw [idem_mul_exp_pow hA hAG hGA (1 / ((q + 1 : ℕ) : ℝ)) q]
  have hne : ((q + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmul : ((q + 1 : ℕ) : ℝ) * (1 / ((q + 1 : ℕ) : ℝ)) = 1 := by field_simp
  rw [hmul, one_smul]

/-! ### A recursion with a small defect -/

/-- The telescoping identity behind `norm_sub_mul_pow_le`. -/
theorem sub_mul_pow_eq_sum (Y : ℕ → 𝔸) (D A : 𝔸) (hY0 : Y 0 = A) (m : ℕ) :
    Y m - A * D ^ m = ∑ j ∈ Finset.range m, (Y (j + 1) - Y j * D) * D ^ (m - 1 - j) := by
  induction m with
  | zero => simp [hY0]
  | succ p ih =>
    have hsplit : Y (p + 1) - A * D ^ (p + 1)
        = (Y (p + 1) - Y p * D) + (Y p - A * D ^ p) * D := by
      rw [sub_mul, pow_succ, ← mul_assoc]
      abel
    rw [hsplit, ih, Finset.sum_mul, Finset.sum_range_succ]
    have hlast : p + 1 - 1 - p = 0 := by omega
    rw [hlast, pow_zero, mul_one, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hjp : j < p := Finset.mem_range.mp hj
    rw [mul_assoc, ← pow_succ]
    congr 2
    omega

/-- **A recursion run `m` times with defect `ε` is within `mεM` of its exact solution**, where
`M` bounds the powers of the comparison operator.  At `ε = O(N⁻²)` and `m = N` this is
`O(N⁻¹)`, which is why an `O(N⁻²)` one-step expansion suffices. -/
theorem norm_sub_mul_pow_le {Y : ℕ → 𝔸} {D A : 𝔸} {M eps : ℝ} (hY0 : Y 0 = A) (m : ℕ)
    (hD : ∀ i, i ≤ m → ‖D ^ i‖ ≤ M) (hrec : ∀ n, n < m → ‖Y (n + 1) - Y n * D‖ ≤ eps)
    (heps : 0 ≤ eps) : ‖Y m - A * D ^ m‖ ≤ m * eps * M := by
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hD 0 (Nat.zero_le m))
  rw [sub_mul_pow_eq_sum Y D A hY0 m]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ j ∈ Finset.range m,
      ‖(Y (j + 1) - Y j * D) * D ^ (m - 1 - j)‖ ≤ eps * M := by
    intro j hj
    have hjm : j < m := Finset.mem_range.mp hj
    exact le_trans (norm_mul_le _ _)
      (mul_le_mul (hrec j hjm) (hD _ (by omega)) (norm_nonneg _) heps)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [mul_assoc]

/-! ### The off-range part dies in one generation -/

/-- **`(1 - A)P` is as small as the perturbation**, because `A - A² = 0` cancels the leading
term outright.  Nothing outside the projection's range survives even a single generation, and
this one line is what forces `ABA` in place of `B` in the limit. -/
theorem norm_one_sub_mul_le {A P : 𝔸} (hA : A * A = A) (hAn : ‖A‖ ≤ 1) :
    ‖(1 - A) * P‖ ≤ (1 + ‖A‖) * ‖P - A‖ := by
  have hrw : (1 - A) * P = (1 - A) * (P - A) := by
    have hexp : (1 - A) * (P - A) = (1 - A) * P - (A - A * A) := by noncomm_ring
    rw [hexp, hA]
    simp
  rw [hrw]
  refine le_trans (norm_mul_le _ _) ?_
  gcongr
  exact le_trans (norm_sub_le _ _) (by simp)

/-- The same on the right. -/
theorem norm_mul_one_sub_le {A P : 𝔸} (hA : A * A = A) :
    ‖P * (1 - A)‖ ≤ (1 + ‖A‖) * ‖P - A‖ := by
  have hrw : P * (1 - A) = (P - A) * (1 - A) := by
    have hexp : (P - A) * (1 - A) = P * (1 - A) - (A - A * A) := by noncomm_ring
    rw [hexp, hA]
    simp
  rw [hrw]
  refine le_trans (norm_mul_le _ _) ?_
  rw [mul_comm]
  gcongr
  exact le_trans (norm_sub_le _ _) (by simp)

/-- **After any number of generations the operator is its own sandwich**, up to the size of a
single generation's perturbation.  `P^n - A P^n A = (1 - A)P^n + A P^n (1 - A)`, and both
pieces factor through a `(1 - A)P` or a `P(1 - A)`. -/
theorem norm_pow_sub_sandwich_le {A P : 𝔸} (hA : A * A = A) (hAn : ‖A‖ ≤ 1)
    (hP : ‖P‖ ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖P ^ n - A * P ^ n * A‖ ≤ 4 * ‖P - A‖ := by
  have hpow : ∀ i : ℕ, ‖P ^ i‖ ≤ 1 := by
    intro i
    rcases Nat.eq_zero_or_pos i with h | h
    · simp [h]
    · exact le_trans (norm_pow_le' P h) (pow_le_one₀ (norm_nonneg P) hP)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsplit : P ^ (m + 1) - A * P ^ (m + 1) * A
      = (1 - A) * P ^ (m + 1) + A * P ^ (m + 1) * (1 - A) := by
    rw [sub_mul, one_mul, mul_sub, mul_one]
    abel
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖(1 - A) * P ^ (m + 1)‖ ≤ 2 * ‖P - A‖ := by
    rw [pow_succ', ← mul_assoc]
    refine le_trans (norm_mul_le _ _) ?_
    have := norm_one_sub_mul_le (A := A) (P := P) hA hAn
    have h2 : (1 + ‖A‖) * ‖P - A‖ ≤ 2 * ‖P - A‖ := by
      gcongr
      linarith
    nlinarith [norm_nonneg ((1 - A) * P), hpow m, norm_nonneg (P ^ m)]
  have h2 : ‖A * P ^ (m + 1) * (1 - A)‖ ≤ 2 * ‖P - A‖ := by
    rw [pow_succ, mul_assoc, mul_assoc]
    refine le_trans (norm_mul_le _ _) ?_
    have hin : ‖P ^ m * (P * (1 - A))‖ ≤ 2 * ‖P - A‖ := by
      refine le_trans (norm_mul_le _ _) ?_
      have := norm_mul_one_sub_le (A := A) (P := P) hA
      have hA2 : (1 + ‖A‖) * ‖P - A‖ ≤ 2 * ‖P - A‖ := by
        gcongr
        linarith
      nlinarith [hpow m, norm_nonneg (P * (1 - A)), norm_nonneg (P ^ m)]
    nlinarith [norm_nonneg (P ^ m * (P * (1 - A))), norm_nonneg (P - A)]
  linarith


/-- Submultiplicativity with explicit bounds on both factors. -/
private theorem norm_mul_le' {x y : 𝔸} {a b : ℝ} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) :
    ‖x * y‖ ≤ a * b :=
  le_trans (norm_mul_le _ _)
    (mul_le_mul hx hy (norm_nonneg _) (le_trans (norm_nonneg _) hx))

/-- **The projection annihilates the off-range part after any number of generations.**  At
`n = 0` exactly, since `A(1 - A) = A - A² = 0`; afterwards because the last factor of `P` is
already within `‖P - A‖` of `A`. -/
theorem norm_idem_mul_pow_mul_one_sub_le {A P : 𝔸} (hA : A * A = A) (hAn : ‖A‖ ≤ 1)
    (hP : ‖P‖ ≤ 1) (n : ℕ) : ‖A * P ^ n * (1 - A)‖ ≤ 2 * ‖P - A‖ := by
  have hpow : ∀ i : ℕ, ‖P ^ i‖ ≤ 1 := by
    intro i
    rcases Nat.eq_zero_or_pos i with h | h
    · simp [h]
    · exact le_trans (norm_pow_le' P h) (pow_le_one₀ (norm_nonneg P) hP)
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    have hz : A * P ^ 0 * (1 - A) = A - A * A := by simp [mul_sub]
    rw [hz, hA, sub_self, norm_zero]
    positivity
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    have hrw : A * P ^ (p + 1) * (1 - A) = A * P ^ p * (P * (1 - A)) := by
      rw [pow_succ, mul_assoc, mul_assoc, mul_assoc]
    rw [hrw]
    have h1 : ‖P * (1 - A)‖ ≤ 2 * ‖P - A‖ := by
      refine le_trans (norm_mul_one_sub_le hA) ?_
      gcongr
      linarith
    have h2 : ‖A * P ^ p‖ ≤ 1 := le_trans (norm_mul_le' hAn (hpow p)) (by norm_num)
    exact le_trans (norm_mul_le' h2 h1) (by rw [one_mul])

/-! ### Möhle's lemma -/

/-- **Möhle's lemma.**  If a generation acts as a projection `A` plus an `O(N⁻¹)` perturbation
`B`, then `N` generations converge to `A · exp(ABA)`.

The three steps are the ones in this module's header: the off-range parts die in a single
generation (`norm_pow_sub_sandwich_le`), the sandwiched chain `A P^n A` satisfies a recursion
whose defect is `O(N⁻²)`, and a recursion with `O(N⁻²)` defect run `N` times lands within
`O(N⁻¹)` of its exact solution (`norm_sub_mul_pow_le`), which `idem_mul_exp_pow` evaluates in
closed form.

`A = 1` recovers K-G (2.14): the projection is trivial exactly when nothing happens on the
fast time scale, and then `ABA = B`.

    Empirical status: NOT AN EMPIRICAL CLAIM -- a theorem about operators.  What is
    empirical is whether a given population's one-generation operator has this form,
    which is a question about its reproduction, not about this lemma. -/
theorem mohle_limit (A B : 𝔸) (hA : A * A = A) (hAn : ‖A‖ ≤ 1) (C : ℝ) (hC : 0 ≤ C)
    (P : ℕ → 𝔸) (hP : ∀ N, ‖P N‖ ≤ 1)
    (hexp : ∀ᶠ N in atTop, ‖P N - (A + (1 / (N : ℝ)) • B)‖ ≤ C / (N : ℝ) ^ 2) :
    Tendsto (fun N : ℕ ↦ P N ^ N) atTop (nhds (A * exp ℝ (A * B * A))) := by
  set G : 𝔸 := A * B * A with hGdef
  have hAG : A * G = G := by
    simp only [hGdef]
    have h : A * (A * B * A) = A * A * B * A := by noncomm_ring
    rw [h, hA]
  have hGA : G * A = G := by
    simp only [hGdef]
    have h : A * B * A * A = A * B * (A * A) := by noncomm_ring
    rw [h, hA]
  have hB0 : (0 : ℝ) ≤ ‖B‖ := norm_nonneg B
  have hG0 : (0 : ℝ) ≤ ‖G‖ := norm_nonneg G
  have hexpG : (0 : ℝ) < Real.exp ‖G‖ := Real.exp_pos _
  set K : ℝ := 4 * (‖B‖ + C) + (2 * (‖B‖ + C) * ‖B‖ + C + ‖G‖ ^ 2) * Real.exp ‖G‖ with hK
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ᶠ N : ℕ in atTop, ‖P N ^ N - A * exp ℝ G‖ ≤ K / (N : ℝ) := by
    filter_upwards [hexp, eventually_ge_atTop (max 1 ⌈‖G‖⌉₊)] with N hcl hN
    have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hNR1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hs0 : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    have hs1 : (1 : ℝ) / (N : ℝ) ≤ 1 := by rw [div_le_one hNR]; exact hNR1
    have hCs : C / (N : ℝ) ^ 2 = C * (1 / (N : ℝ)) ^ 2 := by field_simp
    -- the perturbation is O(1/N)
    have hE : ‖P N - A‖ ≤ (‖B‖ + C) * (1 / (N : ℝ)) := by
      have hsplit : P N - A = (P N - (A + (1 / (N : ℝ)) • B)) + (1 / (N : ℝ)) • B := by abel
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      have h2 : ‖(1 / (N : ℝ)) • B‖ = (1 / (N : ℝ)) * ‖B‖ := by
        rw [norm_smul, Real.norm_of_nonneg hs0.le]
      have h3 : C / (N : ℝ) ^ 2 ≤ C * (1 / (N : ℝ)) := by
        rw [hCs, sq]
        nlinarith [mul_le_mul_of_nonneg_left hs1 (mul_nonneg hC hs0.le)]
      have hring : (‖B‖ + C) * (1 / (N : ℝ)) = C * (1 / (N : ℝ)) + 1 / (N : ℝ) * ‖B‖ := by
        ring
      rw [h2, hring]
      linarith [hcl, h3]
    -- the comparison operator
    set D : 𝔸 := A * exp ℝ ((1 / (N : ℝ)) • G) with hD
    have hsG : ‖(1 / (N : ℝ)) • G‖ ≤ 1 := by
      rw [norm_smul, Real.norm_of_nonneg hs0.le, div_mul_eq_mul_div, one_mul, div_le_one hNR]
      have hceil : ⌈‖G‖⌉₊ ≤ N := le_trans (le_max_right _ _) hN
      exact le_trans (Nat.le_ceil ‖G‖) (by exact_mod_cast hceil)
    have hDpow : ∀ i : ℕ, i ≤ N → ‖D ^ i‖ ≤ Real.exp ‖G‖ := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h
        simpa using Real.one_le_exp hG0
      · obtain ⟨q, rfl⟩ : ∃ q, i = q + 1 := ⟨i - 1, by omega⟩
        rw [hD, idem_mul_exp_pow hA hAG hGA (1 / (N : ℝ)) q]
        refine le_trans (norm_mul_le' hAn (norm_exp_le_exp_norm _)) ?_
        rw [one_mul]
        refine Real.exp_le_exp.mpr ?_
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        have hq : ((q + 1 : ℕ) : ℝ) * (1 / (N : ℝ)) ≤ 1 := by
          rw [mul_one_div, div_le_one hNR]
          exact_mod_cast hi
        nlinarith
    -- the sandwiched chain and its recursion
    set Y : ℕ → 𝔸 := fun n ↦ A * P N ^ n * A with hY
    have hY0 : Y 0 = A := by simp [hY, hA]
    have hpowP : ∀ i : ℕ, ‖P N ^ i‖ ≤ 1 := by
      intro i
      rcases Nat.eq_zero_or_pos i with h | h
      · simp [h]
      · exact le_trans (norm_pow_le' (P N) h) (pow_le_one₀ (norm_nonneg _) (hP N))
    have hAPn : ∀ n : ℕ, ‖A * P N ^ n‖ ≤ 1 := fun n ↦
      le_trans (norm_mul_le' hAn (hpowP n)) (by norm_num)
    have hYn1 : ∀ n : ℕ, ‖Y n‖ ≤ 1 := by
      intro n
      simp only [hY]
      exact le_trans (norm_mul_le' (hAPn n) hAn) (by norm_num)
    have hrho : ‖D - (A + (1 / (N : ℝ)) • G)‖ ≤ ‖G‖ ^ 2 * (1 / (N : ℝ)) ^ 2 := by
      have hrw : D - (A + (1 / (N : ℝ)) • G)
          = A * (exp ℝ ((1 / (N : ℝ)) • G) - 1 - (1 / (N : ℝ)) • G) := by
        rw [hD, mul_sub, mul_sub, mul_one, mul_smul_comm, hAG]
        abel
      rw [hrw]
      have hbnd := norm_exp_sub_one_sub_self_le_sq (x := (1 / (N : ℝ)) • G) hsG
      have hns : ‖(1 / (N : ℝ)) • G‖ ^ 2 = (1 / (N : ℝ)) ^ 2 * ‖G‖ ^ 2 := by
        rw [norm_smul, Real.norm_of_nonneg hs0.le, mul_pow]
      rw [hns] at hbnd
      refine le_trans (norm_mul_le' hAn hbnd) ?_
      rw [one_mul]
      ring_nf
      exact le_refl _
    set eps : ℝ := (2 * (‖B‖ + C) * ‖B‖ + C + ‖G‖ ^ 2) * (1 / (N : ℝ)) ^ 2 with heps
    have heps0 : 0 ≤ eps := by rw [heps]; positivity
    have hrec : ∀ n : ℕ, n < N → ‖Y (n + 1) - Y n * D‖ ≤ eps := by
      intro n _
      have hAAA : A * P N ^ n * A * A = A * P N ^ n * A := by
        rw [mul_assoc (A * P N ^ n) A A, hA]
      have e1 : Y (n + 1) = Y n + A * P N ^ n * (P N - A) * A := by
        simp only [hY]
        rw [pow_succ]
        have h : A * (P N ^ n * P N) * A
            = A * P N ^ n * A * A + A * P N ^ n * (P N - A) * A := by noncomm_ring
        rw [h, hAAA]
      have hYnA : Y n * A = Y n := by simp only [hY]; exact hAAA
      have hYnG : Y n * G = A * P N ^ n * A * B * A := by
        simp only [hY, hGdef]
        have h : A * P N ^ n * A * (A * B * A) = A * P N ^ n * (A * A) * B * A := by
          noncomm_ring
        rw [h, hA]
      have e2 : Y n * (A + (1 / (N : ℝ)) • G)
          = Y n + (1 / (N : ℝ)) • (A * P N ^ n * A * B * A) := by
        rw [mul_add, hYnA, mul_smul_comm, hYnG]
      have e3 : A * P N ^ n * (P N - A) * A
          = (1 / (N : ℝ)) • (A * P N ^ n * B * A)
            + A * P N ^ n * (P N - (A + (1 / (N : ℝ)) • B)) * A := by
        have hd : P N - A = (1 / (N : ℝ)) • B + (P N - (A + (1 / (N : ℝ)) • B)) := by abel
        rw [hd, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
      have e4 : A * P N ^ n * (1 - A) * B * A
          = A * P N ^ n * B * A - A * P N ^ n * A * B * A := by noncomm_ring
      have hkey : Y (n + 1) - Y n * D
          = (1 / (N : ℝ)) • (A * P N ^ n * (1 - A) * B * A)
            + A * P N ^ n * (P N - (A + (1 / (N : ℝ)) • B)) * A
            - Y n * (D - (A + (1 / (N : ℝ)) • G)) := by
        have hDsplit : Y n * (D - (A + (1 / (N : ℝ)) • G))
            = Y n * D - Y n * (A + (1 / (N : ℝ)) • G) := by rw [mul_sub]
        rw [hDsplit, e1, e2, e3, e4, smul_sub]
        abel
      rw [hkey]
      -- three bounds, each O(N⁻²)
      have b1 : ‖(1 / (N : ℝ)) • (A * P N ^ n * (1 - A) * B * A)‖
          ≤ (1 / (N : ℝ)) * (2 * ((‖B‖ + C) * (1 / (N : ℝ))) * ‖B‖) := by
        rw [norm_smul, Real.norm_of_nonneg hs0.le]
        refine mul_le_mul_of_nonneg_left ?_ hs0.le
        have hin : ‖A * P N ^ n * (1 - A)‖ ≤ 2 * ((‖B‖ + C) * (1 / (N : ℝ))) :=
          le_trans (norm_idem_mul_pow_mul_one_sub_le hA hAn (hP N) n) (by linarith)
        have h1 : ‖A * P N ^ n * (1 - A) * B‖ ≤ 2 * ((‖B‖ + C) * (1 / (N : ℝ))) * ‖B‖ :=
          norm_mul_le' hin (le_refl _)
        refine le_trans (norm_mul_le' h1 hAn) ?_
        nlinarith [hs0.le, norm_nonneg (A * P N ^ n * (1 - A))]
      have b2 : ‖A * P N ^ n * (P N - (A + (1 / (N : ℝ)) • B)) * A‖
          ≤ C * (1 / (N : ℝ)) ^ 2 := by
        have hmid : ‖A * P N ^ n * (P N - (A + (1 / (N : ℝ)) • B))‖ ≤ 1 * (C * (1 / (N:ℝ)) ^ 2) :=
          norm_mul_le' (hAPn n) (by rw [← hCs]; exact hcl)
        refine le_trans (norm_mul_le' hmid hAn) ?_
        nlinarith [hs0.le, sq_nonneg (1 / (N : ℝ))]
      have b3 : ‖Y n * (D - (A + (1 / (N : ℝ)) • G))‖ ≤ ‖G‖ ^ 2 * (1 / (N : ℝ)) ^ 2 := by
        refine le_trans (norm_mul_le' (hYn1 n) hrho) ?_
        rw [one_mul]
      have htri := norm_sub_le
        ((1 / (N : ℝ)) • (A * P N ^ n * (1 - A) * B * A)
          + A * P N ^ n * (P N - (A + (1 / (N : ℝ)) • B)) * A)
        (Y n * (D - (A + (1 / (N : ℝ)) • G)))
      have htri2 := norm_add_le ((1 / (N : ℝ)) • (A * P N ^ n * (1 - A) * B * A))
        (A * P N ^ n * (P N - (A + (1 / (N : ℝ)) • B)) * A)
      rw [heps]
      nlinarith [hs0.le]
    -- assemble
    have hmain := norm_sub_mul_pow_le (Y := Y) (D := D) (A := A) (M := Real.exp ‖G‖)
      (eps := eps) hY0 N hDpow hrec heps0
    have hDN : A * D ^ N = A * exp ℝ G := by
      rw [hD, idem_mul_exp_pow_self hA hAG hGA hN1, ← mul_assoc, hA]
    rw [hDN] at hmain
    have hsand : ‖P N ^ N - Y N‖ ≤ 4 * ‖P N - A‖ := by
      simp only [hY]
      exact norm_pow_sub_sandwich_le hA hAn (hP N) hN1
    have htri : ‖P N ^ N - A * exp ℝ G‖ ≤ ‖P N ^ N - Y N‖ + ‖Y N - A * exp ℝ G‖ := by
      have h := norm_add_le (P N ^ N - Y N) (Y N - A * exp ℝ G)
      simpa using h
    have hNeps : (N : ℝ) * eps * Real.exp ‖G‖
        = ((2 * (‖B‖ + C) * ‖B‖ + C + ‖G‖ ^ 2) * Real.exp ‖G‖) / (N : ℝ) := by
      rw [heps]
      field_simp
    rw [hNeps] at hmain
    have hEN : 4 * ‖P N - A‖ ≤ (4 * (‖B‖ + C)) / (N : ℝ) := by
      rw [le_div_iff₀ hNR]
      have hmul := mul_le_mul_of_nonneg_right hE hNR.le
      have hclear : (‖B‖ + C) * (1 / (N : ℝ)) * (N : ℝ) = ‖B‖ + C := by field_simp
      rw [hclear] at hmul
      nlinarith [hmul]
    rw [hK, add_div]
    linarith
  refine squeeze_zero' (g := fun N : ℕ ↦ K / (N : ℝ)) ?_ hbound ?_
  · filter_upwards with N
    exact norm_nonneg _
  · have h := tendsto_one_div_atTop_nhds_zero_nat.const_mul K
    simpa [mul_one_div] using h

end Coalescent

end Descent
