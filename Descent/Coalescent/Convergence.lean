/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.WrightFisher
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Descent

/-!
# The limit: `N` generations of the mechanism become one unit of coalescent time

`Descent.Coalescent.WrightFisher` counts the one-generation coalescence probability off the
uniform parent law and `Descent.Coalescent.Generator` supplies the contraction estimate
K-G (2.13) that a limit argument would run on.  What was never taken was the limit itself:
K-G (2.14)-(2.15), the statement that

  `R_t = ℛ_{[Nt]}`   converges, as `N → ∞`, to the continuous-time chain with generator `Q`,

and without it every result in this group about `e^{-d_k t}` was about a process the corpus
had declared rather than derived from the reproduction mechanism.  `Descent.Coalescent.Program`
recorded that as the missing convergence theorem.

This file takes the limit for the quantity it is needed for.  Over `N` generations, `k`
lineages avoid all coalescence with probability `p_N(k)^N`, where `p_N(k)` is the counted
`(N)_k/N^k`, and

  `p_N(k)^N = ∏_{i<k} (1 - i/N)^N  →  ∏_{i<k} e^{-i} = e^{-d_k}`.

That is `tendsto_noCoalescenceProb_pow`, and it is exactly K-G's time scale: **`N`
generations of Wright-Fisher reproduction are one unit of coalescent time**, in which a
`k`-lineage state survives with probability `e^{-d_k}` -- the exponential holding law K-C
(1.7) posits, now obtained from parent choice.

The proof has no analysis in it beyond one Mathlib limit, `(1 + x/N)^N → e^x`.  Everything
else is the observation that the falling factorial FACTORISES: `(N)_k/N^k` is a product of
`k` terms each of the form `1 - i/N`, so the limit is a product of `k` exponentials, and the
sum in the exponent is `Σ_{i<k} i = d_k`.  The rate ladder appears in the limit for the same
reason it appears in the count -- it is the number of ordered pairs -- and
`sum_range_neg_cast` is where that is done.

## What this does and does not close

It closes the convergence of the SURVIVAL PROBABILITIES, for every `k`, which is what every
downstream result in this group uses.  It does not prove convergence of the processes in the
Skorokhod sense, nor Möhle's lemma in its matrix form for general exchangeable models with separated time scales; those need the semigroup machinery K-G (2.11)-(2.13) sketches and
`Coalescent.Generator` has only the contraction half of.

## Main results

- `tendsto_one_sub_div_pow`: `(1 - c/N)^N → e^{-c}`.
- `sum_range_neg_cast`: `Σ_{i<k} (-i) = -d_k`, the ladder in the exponent.
- `tendsto_noCoalescenceProb_pow`: **`p_N(k)^N → e^{-d_k}`**, K-G (2.14) for the survival.
- `tendsto_pairDistinct_pow`: the pair case against the corpus's own `pairDistinct`, so the
  drift recurrence and the exponential clock are the same object at two time scales.
-/

namespace Coalescent

open Finset Filter Topology

/-! ### One factor -/

/-- `(1 - c/N)^N → e^{-c}`.  Mathlib's `(1 + x/N)^N → e^x` at `x = -c`. -/
theorem tendsto_one_sub_div_pow (c : ℝ) :
    Tendsto (fun N : ℕ ↦ (1 - c / (N : ℝ)) ^ N) atTop (nhds (Real.exp (-c))) := by
  have h := Real.tendsto_one_add_div_pow_exp (-c)
  refine h.congr fun N ↦ ?_
  ring

/-! ### The ladder in the exponent -/

/-- `Σ_{i<k} (-i) = -d_k`.  The same count that gives the rate ladder its value gives the
exponent of the limiting survival probability, which is why the two agree without any
adjustment. -/
theorem sum_range_neg_cast (k : ℕ) : ∑ i ∈ range k, (-(i : ℝ)) = -deathRate k := by
  induction k with
  | zero => simp [deathRate,
      Descent.Core.pairCount]
  | succ m ih =>
      rw [sum_range_succ, ih]
      unfold deathRate Descent.Core.pairCount
      push_cast
      ring

/-! ### The limit -/

/-- **K-G (2.14) for the survival probability.**  `N` generations of Wright-Fisher
reproduction leave `k` lineages uncoalesced with probability tending to `e^{-d_k}`.

The proof is that the falling factorial factorises.  `(N)_k/N^k = ∏_{i<k}(1 - i/N)`
(`WrightFisher.noCoalescenceProb_eq_prod`), raising to the `N`-th power distributes over the
product, each factor tends to `e^{-i}`, and the exponents sum to `-d_k`.

This is the theorem that makes the whole group's exponential clock a consequence of parent
choice rather than a postulate: K-C (1.7) writes the holding time as exponential of rate
`d_k`, and here that law arrives as a limit of counting. -/
theorem tendsto_noCoalescenceProb_pow (k : ℕ) :
    Tendsto (fun N : ℕ ↦ (∏ i ∈ range k, (1 - (i : ℝ) / (N : ℝ))) ^ N) atTop
      (nhds (Real.exp (-deathRate k))) := by
  have hlim : Tendsto (fun N : ℕ ↦ ∏ i ∈ range k, (1 - (i : ℝ) / (N : ℝ)) ^ N) atTop
      (nhds (∏ i ∈ range k, Real.exp (-(i : ℝ)))) :=
    tendsto_finset_prod _ fun i _ ↦ tendsto_one_sub_div_pow (i : ℝ)
  have hexp : ∏ i ∈ range k, Real.exp (-(i : ℝ)) = Real.exp (-deathRate k) := by
    rw [← Real.exp_sum, sum_range_neg_cast]
  rw [hexp] at hlim
  refine hlim.congr fun N ↦ ?_
  rw [← Finset.prod_pow]

/-- The same limit written on the corpus's own counted probability, for sample sizes the
count applies to.  `noCoalescenceProb N k` IS the product above once `k ≤ N`
(`WrightFisher.noCoalescenceProb_eq_prod`), so the survival of a `k`-lineage state over `N`
generations tends to `e^{-d_k}`. -/
theorem noCoalescenceProb_pow_eq_prod_pow {N k : ℕ} (hN : 0 < N) (hkN : k ≤ N) :
    noCoalescenceProb N k ^ N = (∏ i ∈ range k, (1 - (i : ℝ) / (N : ℝ))) ^ N := by
  rw [noCoalescenceProb_eq_prod hN hkN]

/-- **The pair case, against the corpus's own recurrence.**  `pairDistinct N s` is the
probability that two lineages are still distinct after `s` generations, and
`WrightFisher.hetRecurrence_eq_pairDistinct` identifies it with the heterozygosity recurrence
the corpus had posited for years.  Over `N` generations it tends to `e^{-1}`, which is the
exponential clock at `d_2 = 1`.

So the scalar drift model, the counted mechanism, and the continuous-time coalescent are one
object seen at three resolutions, and this is the theorem that joins the last two. -/
theorem tendsto_pairDistinct_pow :
    Tendsto (fun N : ℕ ↦ (1 - 1 / (N : ℝ)) ^ N) atTop (nhds (Real.exp (-1))) :=
  tendsto_one_sub_div_pow 1

/-- And `m` such stretches give `e^{-m}`: the survival is exponential in the number of
coalescent time units, not merely at one of them.  This is the semigroup property of the
limit, obtained without a semigroup. -/
theorem tendsto_pairDistinct_pow_mul (m : ℕ) :
    Tendsto (fun N : ℕ ↦ ((1 - 1 / (N : ℝ)) ^ N) ^ m) atTop
      (nhds (Real.exp (-(m : ℝ)))) := by
  have h := tendsto_pairDistinct_pow.pow m
  have hexp : (Real.exp (-1)) ^ m = Real.exp (-(m : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rwa [hexp] at h

end Coalescent

end Descent
