/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Generator
import Descent.Coalescent.ExpRemainder
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Tactic

namespace Descent

/-!
# K-G (2.14): `P_N^{N} → exp Q`

`Descent.Coalescent.Generator` proves the contraction estimate K-G (2.13) --
`‖A₁⋯A_r - B₁⋯B_r‖ ≤ Σ ‖A_s - B_s‖`, and its single-pair corollary
`‖A^r - B^r‖ ≤ r ‖A - B‖` -- and says in its own docstring that this is "the form K-G (2.14)
uses".  It then stops, because K-G (2.14) is a limit and the file had no limit in it.
`Descent.Coalescent.Convergence` later took the limit for the SURVIVAL PROBABILITIES, one
scalar at a time.  This file takes it for the operator, which is what K-G actually states.

The argument is three lines once the estimate is available, and the reason it is three lines
is that the time scale is chosen to make it so.  Over `N` generations,

  `‖P_N^N - exp(N⁻¹Q)^N‖ ≤ N ‖P_N - exp(N⁻¹Q)‖ ≤ N · C/N² = C/N`,

and `exp(N⁻¹Q)^N` is `exp(Q)` exactly -- no approximation, because `N • (N⁻¹ • Q) = Q`.  So
the semigroup limit needs no continuity argument at all at `t = 1`; the `N` copies of the
one-generation error accumulate to `O(N⁻¹)` and vanish.

That `t = 1` is the whole of it is worth saying.  `N` generations of reproduction ARE one
unit of coalescent time (K-G (2.15)), so the limit at `t = 1` plus the semigroup property is
the limit at every `t`; nothing about the argument is special to the exponent.

## What is proved, and what is not

PROVED, in the generality K-G states it: for any complete normed algebra, any `Q`, and any
family `P_N` of contractions within `C/N²` of `exp(N⁻¹Q)`, the `N`-th powers converge to
`exp Q`.  The hypotheses are exactly K-G's -- `P_N` stochastic, `exp(N⁻¹Q)` stochastic because
`Q` is a `Q`-matrix (`Generator.generator_row_sum_zero`), and `P_N = I + N⁻¹Q + O(N⁻²)`.

NOT PROVED: the instantiation at the coalescent's own transition matrix, because this corpus
has the chain as a KERNEL (`Kernel.jumpKernel`) and not as a matrix, so there is no `P_N` to
feed the theorem.  `WrightFisher.coalescenceProb_le` bounds the entries and
`Convergence.tendsto_noCoalescenceProb_pow` takes the entrywise limit; assembling those into
an operator bound is the missing step, and it is bookkeeping about matrices rather than
about genealogy.  Nor is Möhle's lemma proper -- the `A + B/N` form with `A` a projection,
for models whose time scales separate -- which is a different theorem with a different limit.

## Main results

- `norm_pow_sub_pow_le`: `‖A^r - B^r‖ ≤ r‖A - B‖`, `Generator`'s estimate on powers.
- `exp_smul_pow_self`: `exp(N⁻¹Q)^N = exp Q`, exactly.
- `tendsto_pow_of_close`: the limit with the comparison family left open.
- `tendsto_pow_self_exp`: **K-G (2.14)**.
-/

namespace Coalescent

open Filter Topology NormedSpace

/-- `‖A^r - B^r‖ ≤ r ‖A - B‖` for contractions, which is `Generator.pow_sub_pow_le` written
on powers rather than on ordered products. -/
theorem norm_pow_sub_pow_le {M : Type*} [NormedRing M] [NormOneClass M] (A B : M)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (r : ℕ) :
    ‖A ^ r - B ^ r‖ ≤ (r : ℝ) * ‖A - B‖ := by
  have h := pow_sub_pow_le A B hA hB r
  rwa [prodUpTo_const A r, prodUpTo_const B r] at h

/-- **`exp(N⁻¹Q)^N = exp Q`, exactly.**  The `N` copies of the one-generation semigroup
compose to the whole unit of coalescent time with no error, which is why K-G's argument has
only one approximation in it. -/
theorem exp_smul_pow_self {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (Q : 𝔸) {N : ℕ} (hN : 0 < N) :
    exp ℝ ((1 / (N : ℝ)) • Q) ^ N = exp ℝ Q := by
  have hNne : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    linarith
  have hcoef : ((N : ℝ)) * (1 / (N : ℝ)) = 1 := by field_simp
  have hsmul : (N : ℕ) • ((1 / (N : ℝ)) • Q) = Q := by
    rw [← Nat.cast_smul_eq_nsmul ℝ N ((1 / (N : ℝ)) • Q), smul_smul, hcoef, one_smul]
  rw [← exp_nsmul (𝕂 := ℝ) N ((1 / (N : ℝ)) • Q), hsmul]

/-- **The limit, with the comparison family left open.**  If `P_N` is a contraction within
`C/N²` of a contraction `B_N` whose `N`-th power is a FIXED `L`, then `P_N^N → L`.

This is the whole of K-G's argument: the `N` copies of a one-generation error of size `C/N²`
accumulate to `C/N` and vanish, and the comparison family contributes nothing because its
`N`-th power does not move.  Taking `B_N = exp(N⁻¹Q)` gives `tendsto_pow_self_exp`; taking a
family that satisfies a semigroup law directly -- which for a two-state generator is
elementary algebra, `Descent.Coalescent.PairChainLimit` -- avoids computing a matrix
exponential at all. -/
theorem tendsto_pow_of_close {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] (L : 𝔸) (C : ℝ)
    (P B : ℕ → 𝔸)
    (hP : ∀ N, ‖P N‖ ≤ 1) (hB : ∀ N, ‖B N‖ ≤ 1)
    (hpow : ∀ N : ℕ, 1 ≤ N → B N ^ N = L) (hC : 0 ≤ C)
    (hclose : ∀ᶠ N in atTop, ‖P N - B N‖ ≤ C / (N : ℝ) ^ 2) :
    Tendsto (fun N : ℕ ↦ P N ^ N) atTop (nhds L) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ᶠ N in atTop, ‖P N ^ N - L‖ ≤ C / (N : ℝ) := by
    filter_upwards [hclose, eventually_ge_atTop 1] with N hcl hN
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hstep := norm_pow_sub_pow_le (P N) (B N) (hP N) (hB N) N
    rw [hpow N hN] at hstep
    have hmul : (N : ℝ) * ‖P N - B N‖ ≤ (N : ℝ) * (C / (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hcl (le_of_lt hNR)
    have hsimp : (N : ℝ) * (C / (N : ℝ) ^ 2) = C / (N : ℝ) := by
      field_simp
    rw [hsimp] at hmul
    linarith
  have hg : Tendsto (fun N : ℕ ↦ C / (N : ℝ)) atTop (nhds 0) := by
    have h := tendsto_one_div_atTop_nhds_zero_nat.const_mul C
    simpa [mul_one_div] using h
  refine squeeze_zero' (g := fun N : ℕ ↦ C / (N : ℝ)) ?_ hbound hg
  · filter_upwards with N
    exact norm_nonneg _

/-- **K-G (2.14).**  If each generation's operator is a contraction within `C/N²` of
`exp(N⁻¹Q)`, then `N` generations converge to `exp Q`.

The hypotheses are K-G's own: `P_N` stochastic (a contraction), `exp(N⁻¹Q)` stochastic
because `Q` is a `Q`-matrix, and the one-generation expansion `P_N = I + N⁻¹Q + O(N⁻²)` in the
form of a distance bound.  The conclusion is the coalescent semigroup. -/
theorem tendsto_pow_self_exp {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (Q : 𝔸) (C : ℝ) (P : ℕ → 𝔸)
    (hP : ∀ N, ‖P N‖ ≤ 1)
    (hE : ∀ N : ℕ, ‖exp ℝ ((1 / (N : ℝ)) • Q)‖ ≤ 1)
    (hclose : ∀ N, ‖P N - exp ℝ ((1 / (N : ℝ)) • Q)‖ ≤ C / (N : ℝ) ^ 2) :
    Tendsto (fun N : ℕ ↦ P N ^ N) atTop (nhds (exp ℝ Q)) := by
  have hC : 0 ≤ C := by
    have h := hclose 1
    have hnn : (0 : ℝ) ≤ ‖P 1 - exp ℝ ((1 / ((1 : ℕ) : ℝ)) • Q)‖ := norm_nonneg _
    have h1 : C / ((1 : ℕ) : ℝ) ^ 2 = C := by norm_num
    linarith [h1 ▸ h]
  refine tendsto_pow_of_close (exp ℝ Q) C P (fun N ↦ exp ℝ ((1 / (N : ℝ)) • Q)) hP hE
    (fun N hN ↦ exp_smul_pow_self Q hN) hC (Filter.Eventually.of_forall hclose)

/-- **K-G (2.11) as the hypothesis, which is how Kingman writes it.**  If the one-generation
operator is `1 + N⁻¹Q + O(N⁻²)` -- not "close to `exp(N⁻¹Q)`", which is a statement nobody
verifies directly -- then `N` generations converge to `exp Q`.

`Descent.Coalescent.ExpRemainder.norm_exp_sub_one_sub_self_le_sq` is what makes the two
hypotheses interchangeable: `1 + N⁻¹Q` and `exp(N⁻¹Q)` differ by at most `‖Q‖²/N²` once
`‖Q‖ ≤ N`, so an expansion to order `N⁻²` is a comparison to order `N⁻²`.

This is the form a transition matrix would be fed to, and the reason the many-state case is
now a counting problem rather than an analytic one. -/
theorem tendsto_pow_of_expansion {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (Q : 𝔸) (C : ℝ) (hC : 0 ≤ C) (P : ℕ → 𝔸)
    (hP : ∀ N : ℕ, ‖P N‖ ≤ 1) (hE : ∀ N : ℕ, ‖exp ℝ ((1 / (N : ℝ)) • Q)‖ ≤ 1)
    (hclose : ∀ N : ℕ, ‖P N - (1 + (1 / (N : ℝ)) • Q)‖ ≤ C / (N : ℝ) ^ 2) :
    Tendsto (fun N : ℕ ↦ P N ^ N) atTop (nhds (exp ℝ Q)) := by
  refine tendsto_pow_of_close (exp ℝ Q) (C + ‖Q‖ ^ 2) P
    (fun N ↦ exp ℝ ((1 / (N : ℝ)) • Q)) hP hE (fun N hN ↦ exp_smul_pow_self Q hN)
    (by positivity) ?_
  filter_upwards [eventually_ge_atTop (max 1 ⌈‖Q‖⌉₊)] with N hN
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hQN : ‖(1 / (N : ℝ)) • Q‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [div_mul_eq_mul_div, one_mul, div_le_one hNR]
    have hceil : ⌈‖Q‖⌉₊ ≤ N := le_trans (le_max_right _ _) hN
    exact le_trans (Nat.le_ceil ‖Q‖) (by exact_mod_cast hceil)
  have hrem : ‖exp ℝ ((1 / (N : ℝ)) • Q) - (1 + (1 / (N : ℝ)) • Q)‖
      ≤ ‖Q‖ ^ 2 / (N : ℝ) ^ 2 := by
    have h := norm_exp_sub_one_sub_self_le_sq (x := (1 / (N : ℝ)) • Q) hQN
    have hnorm : ‖(1 / (N : ℝ)) • Q‖ ^ 2 = ‖Q‖ ^ 2 / (N : ℝ) ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), mul_pow, div_pow, one_pow]
      ring
    rw [hnorm] at h
    have hcomm : exp ℝ ((1 / (N : ℝ)) • Q) - (1 + (1 / (N : ℝ)) • Q)
        = exp ℝ ((1 / (N : ℝ)) • Q) - 1 - (1 / (N : ℝ)) • Q := by abel
    rw [hcomm]
    exact h
  calc ‖P N - exp ℝ ((1 / (N : ℝ)) • Q)‖
      ≤ ‖P N - (1 + (1 / (N : ℝ)) • Q)‖
          + ‖(1 + (1 / (N : ℝ)) • Q) - exp ℝ ((1 / (N : ℝ)) • Q)‖ := by
        have := norm_sub_le (P N - (1 + (1 / (N : ℝ)) • Q))
          ((1 + (1 / (N : ℝ)) • Q) - exp ℝ ((1 / (N : ℝ)) • Q))
        simpa [sub_add_sub_cancel] using norm_sub_le_norm_sub_add_norm_sub
          (P N) (1 + (1 / (N : ℝ)) • Q) (exp ℝ ((1 / (N : ℝ)) • Q))
    _ ≤ C / (N : ℝ) ^ 2 + ‖Q‖ ^ 2 / (N : ℝ) ^ 2 := by
        refine add_le_add (hclose N) ?_
        rw [← norm_neg]
        simpa using hrem
    _ = (C + ‖Q‖ ^ 2) / (N : ℝ) ^ 2 := by ring

end Coalescent

end Descent
