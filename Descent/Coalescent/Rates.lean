/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Descent.Core.Ratios

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# The Kingman coalescent: rates, transit time, and the absorption martingale

This is the arithmetic core of Kingman's two 1982 papers -- *The coalescent*
(Stoch. Proc. Appl. 13, 235-248; cited below as **K-C**) and *On the genealogy of large
populations* (J. Appl. Prob. 19A, 27-43; cited as **K-G**).  Everything here is a statement
about the numbers `d_k = k(k-1)/2`, which K-C (1.7) and K-G (5.4) obtain as the total
transition rate out of a state with `k` blocks.  That those numbers ARE the block-count
rates is a combinatorial fact about the state space, proved separately in
`Descent.Coalescent.StateSpace`; this file takes the ladder as given and works out its
consequences.

Four separate quantities in the two papers are the same telescoping sum, and that is the
reason to put them in one file:

* the mean transit time `E(T_n) = 2 - 2/n`                                    K-G (5.7);
* the finiteness of `T = Σ τ_r`, which is what lets the death process start
  at infinity and so what makes the infinite coalescent exist at all          K-C (2.8);
* the tail mass `Σ_{r ≥ k} d_r⁻¹ = 2/(k-1)`, the entrance-boundary estimate    K-C p.239;
* the product `φ₁(x) = ∏_{r > x} (1 - d_r⁻¹) = (x-1)/(x+1)`, whose associated
  martingale gives the uniform-in-`n` absorption bound                        K-G (5.11)-(5.13).

The last of these is why the constant `3` in K-G (2.4) -- the best-possible factor in the
Wright-Fisher bound on the probability that a whole generation lacks a common ancestor --
is the same `3` that appears as the large-`t` asymptote of the transit-time tail: it is
`1 / inf_{x ≥ 2} φ₁(x)`, and `inf_{x ≥ 2} (x-1)/(x+1) = 1/3` is proved here as
`one_le_three_mul_survivalFactor`.

## Main results

- `one_div_deathRate_add_two` and `sum_one_div_deathRate_range`: the telescoping and its
  exact partial sums, which every result below is a reading of.
- `meanTransitTime_eq_two_sub`: K-G (5.7), `E(T_n) = 2 - 2/n`.
- `meanTransitTime_lt_two`: the bound that is uniform in `n`.
- `hasSum_one_div_deathRate_tail`: K-C p.239, `Σ_{r ≥ k} d_r⁻¹ = 2/(k-1)`.
- `survivalFactor_partialProd` and `tendsto_survivalFactor_partialProd`: K-G (5.11), the
  exact partial products of `∏ (1 - d_r⁻¹)` and their limit `(x-1)/(x+1)`.
- `one_le_three_mul_survivalFactor`: `inf_{x ≥ 2} φ₁(x) = 1/3`, the source of the `3`.
- `measure_two_le_le_three_mul_integral`: K-G (5.13), the absorption bound in the form the
  martingale identity feeds it -- a statement about any integer-valued random variable, so
  it is the coalescent's Markov inequality and not a claim about the coalescent.
-/

namespace Coalescent

open Filter MeasureTheory

/-- Kingman's death rate `d_k = k(k-1)/2`: the total rate at which a coalescent state with `k`
blocks leaves that state.

Empirical status: NOT AN EMPIRICAL CLAIM.  `d_k` is the number of unordered pairs of blocks
times the per-pair rate `1`, and the per-pair rate is `1` by the choice of time unit
(K-G (2.10), where the unit is `N` generations of a Wright-Fisher population, and (4.4),
where a family-size variance `σ²` rescales it to `N σ⁻²`).  What is empirical is whether a
given population's genealogy has ANY such ladder -- multiple-merger regimes do not, and
`Descent.Blindness.MultipleMergerBlindness` records which statistics can tell. -/
noncomputable def deathRate (k : ℕ) : ℝ := Descent.Core.pairCount k

@[simp] theorem deathRate_zero : deathRate 0 = 0 := by norm_num [deathRate,
      Descent.Core.pairCount]

/-- One lineage never coalesces: the absorbing state of the death process.  K-C (1.10). -/
@[simp] theorem deathRate_one : deathRate 1 = 0 := by norm_num [deathRate,
      Descent.Core.pairCount]

@[simp] theorem deathRate_two : deathRate 2 = 1 := by norm_num [deathRate,
      Descent.Core.pairCount]

@[simp] theorem deathRate_three : deathRate 3 = 3 := by norm_num [deathRate,
      Descent.Core.pairCount]

theorem deathRate_succ_succ (k : ℕ) :
    deathRate (k + 2) = ((k : ℝ) + 2) * ((k : ℝ) + 1) / 2 := by
  unfold deathRate Descent.Core.pairCount
  push_cast
  ring

theorem deathRate_pos {k : ℕ} (hk : 2 ≤ k) : 0 < deathRate k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [show 2 + m = m + 2 from by ring, deathRate_succ_succ]
  positivity

/-- Positivity in the form the reciprocal-sum results need it: indexed from the smallest
informative sample, so no side condition has to be carried through a `Finset.range`. -/
theorem deathRate_add_two_pos (k : ℕ) : 0 < deathRate (k + 2) := by
  rw [deathRate_succ_succ]
  positivity

theorem deathRate_ne_zero {k : ℕ} (hk : 2 ≤ k) : deathRate k ≠ 0 :=
  ne_of_gt (deathRate_pos hk)

/-- The reciprocal ladder telescopes, indexed from the smallest informative sample.

This identity is proved here, in the coalescent's own derivation.
`Blindness.SpectrumIdentifiability` reasons about the same `k(k-1)/2` under the name
`coalescentRate` and imports it from here, which is the only direction in which the
derivation can be load-bearing: a 12,000-line derivation resting on an applied module
about spectrum identifiability would be an applied result the derivation cannot do
without. -/
theorem one_div_deathRate_add_two (k : ℕ) :
    1 / deathRate (k + 2) = 2 * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) := by
  have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((k : ℝ) + 2) ≠ 0 := by positivity
  rw [deathRate_succ_succ]
  field_simp
  ring

/-- Exact partial sums of the reciprocal ladder: `Σ_{r=2}^{n+1} d_r⁻¹ = 2 - 2/(n+1)`. -/
theorem sum_one_div_deathRate_range (n : ℕ) :
    ∑ k ∈ Finset.range n, 1 / deathRate (k + 2) = 2 - 2 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
      rw [Finset.sum_range_succ, ih, one_div_deathRate_add_two]
      push_cast
      field_simp
      ring

/-- The reciprocal ladder telescopes.  This single identity is what makes the transit time
finite, the tail mass summable, and the entrance boundary available. -/
theorem one_div_deathRate_eq {r : ℕ} (hr : 2 ≤ r) :
    1 / deathRate r = 2 * (1 / ((r : ℝ) - 1) - 1 / (r : ℝ)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [show 2 + k = k + 2 from by ring, one_div_deathRate_add_two]
  push_cast
  ring

/-! ### The transit time

K-C (1.12) and K-G (5.5) write the transit time as `T_n = Σ_{r=2}^{n} τ_r` with `τ_r`
independent and exponential of rate `d_r`, so `E(τ_r) = d_r⁻¹` (K-G (5.6)).  The mean is
therefore the partial sum of the reciprocal ladder, and that is what `meanTransitTime`
records.  The independence and the exponential law are properties of the process; the sum
of the means is the arithmetic, and it is the arithmetic that carries the two conclusions
Kingman draws -- the bound `2` uniform in `n`, and the convergence that lets `T` exist. -/

/-- `E(T_n)`, the mean transit time of the `n`-coalescent: the sum of `d_r⁻¹` over the
`n - 1` states the block count passes through.  K-G (5.5)-(5.7).

Empirical status: NOT AN EMPIRICAL CLAIM given the ladder; it is `Σ_{r=2}^n d_r⁻¹`
rewritten.  In generations, this is `2 N_e (2 - 2/n)` -- see
`Descent.Core.coalescentTimeScale` for the factor that converts. -/
noncomputable def meanTransitTime (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n - 1), 1 / deathRate (k + 2)

theorem meanTransitTime_succ (n : ℕ) :
    meanTransitTime (n + 1) = 2 - 2 / ((n : ℝ) + 1) := by
  unfold meanTransitTime
  simp only [Nat.add_sub_cancel]
  exact sum_one_div_deathRate_range n

/-- **K-G (5.7): the mean transit time of the `n`-coalescent is `2 - 2/n`.**

In the time unit of K-G (2.15) -- `N` generations of a Wright-Fisher population -- the
expected time back to the most recent common ancestor of a sample of `n` is `2 - 2/n`,
whatever `n` is.  Doubling the sample never adds more than the whole of what is already
there, because the total is capped at `2`. -/
theorem meanTransitTime_eq_two_sub {n : ℕ} (hn : 1 ≤ n) :
    meanTransitTime n = 2 - 2 / (n : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 1 + m = m + 1 from by ring, meanTransitTime_succ]
  push_cast
  ring

/-- A sample of one has already coalesced. -/
@[simp] theorem meanTransitTime_one : meanTransitTime 1 = 0 := by
  simp [meanTransitTime]

/-- A sample of two waits `1`, which is `2 N_e` generations. -/
@[simp] theorem meanTransitTime_two : meanTransitTime 2 = 1 := by
  norm_num [meanTransitTime]

/-- **The bound uniform in `n`.**  However large the sample, its expected time to a common
ancestor is under two.  K-G (5.8): this is why `T = Σ_{r≥2} τ_r` converges, and hence why
the death process can be started from infinity at all. -/
theorem meanTransitTime_lt_two (n : ℕ) : meanTransitTime n < 2 := by
  cases n with
  | zero => norm_num [meanTransitTime]
  | succ m =>
      rw [meanTransitTime_succ]
      have h : 0 < 2 / ((m : ℝ) + 1) := by positivity
      linarith

theorem meanTransitTime_nonneg (n : ℕ) : 0 ≤ meanTransitTime n := by
  unfold meanTransitTime
  refine Finset.sum_nonneg fun k _ ↦ ?_
  exact one_div_nonneg.mpr (deathRate_pos (by omega)).le

/-- The mean transit time increases to `2`: doubling and redoubling the sample buys the
remaining `2/n`, and no more. -/
theorem tendsto_meanTransitTime :
    Tendsto (fun n : ℕ ↦ meanTransitTime (n + 1)) atTop (nhds 2) := by
  have hzero : Tendsto (fun n : ℕ ↦ 2 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
  simpa only [meanTransitTime_succ, sub_zero] using tendsto_const_nhds.sub hzero

/-! ### The tail of the ladder, and the entrance boundary

K-C p.239 records `Σ_{r=k}^{∞} d_r⁻¹ = 2/(k-1)`.  This is the estimate that makes the
"pure death process started at infinity" of K-C (2.8) and K-G (6.1) legitimate: the time
`E_k = Σ_{r>k} τ_r` needed to come down from infinity to `k` lineages has finite mean, so
the process enters from `∞` instantly and is in a finite state at every positive time. -/

/-- A shifted reciprocal tends to zero; used twice below, for the tail sum and for the
product limit. -/
theorem tendsto_two_div_shift {c : ℝ} (hc : 2 ≤ c) :
    Tendsto (fun m : ℕ ↦ 2 / (c + (m : ℝ) - 1)) atTop (nhds 0) := by
  have hlim : Tendsto (fun m : ℕ ↦ 2 * (1 / ((m : ℝ) + 1))) atTop (nhds 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
  refine squeeze_zero (fun m ↦ ?_) (fun m ↦ ?_) hlim
  · have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hpos : (0 : ℝ) < c + (m : ℝ) - 1 := by linarith
    positivity
  · have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hle : 2 / (c + (m : ℝ) - 1) ≤ 2 / ((m : ℝ) + 1) := by
      gcongr <;> linarith
    simpa [mul_one_div] using hle

/-- Exact partial sums of the tail ladder. -/
theorem sum_one_div_deathRate_tail {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    ∑ j ∈ Finset.range m, 1 / deathRate (k + j)
      = 2 / ((k : ℝ) - 1) - 2 / ((k : ℝ) + (m : ℝ) - 1) := by
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  induction m with
  | zero => norm_num
  | succ m ih =>
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hkm : (2 : ℕ) ≤ k + m := le_trans hk (Nat.le_add_right k m)
      have h1 : ((k : ℝ) - 1) ≠ 0 := by linarith
      have h2 : ((k : ℝ) + (m : ℝ) - 1) ≠ 0 := by linarith
      have h3 : ((k : ℝ) + (m : ℝ)) ≠ 0 := by linarith
      rw [Finset.sum_range_succ, ih, one_div_deathRate_eq hkm]
      push_cast
      ring

/-- **K-C p.239: `Σ_{r ≥ k} d_r⁻¹ = 2/(k-1)`.**  The mean time to come down from infinitely
many lineages to `k` of them.  For `k = 2` it is `2`, the mean of the transit time `T`
itself, matching `meanTransitTime_lt_two` in the limit. -/
theorem hasSum_one_div_deathRate_tail {k : ℕ} (hk : 2 ≤ k) :
    HasSum (fun j : ℕ ↦ 1 / deathRate (k + j)) (2 / ((k : ℝ) - 1)) := by
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun j ↦ one_div_nonneg.mpr (deathRate_pos (le_trans hk (Nat.le_add_right k j))).le)]
  simpa only [sum_one_div_deathRate_tail hk, sub_zero] using
    tendsto_const_nhds.sub (tendsto_two_div_shift hk')

theorem summable_one_div_deathRate_tail {k : ℕ} (hk : 2 ≤ k) :
    Summable fun j : ℕ ↦ 1 / deathRate (k + j) :=
  (hasSum_one_div_deathRate_tail hk).summable

theorem tsum_one_div_deathRate_tail {k : ℕ} (hk : 2 ≤ k) :
    ∑' j : ℕ, 1 / deathRate (k + j) = 2 / ((k : ℝ) - 1) :=
  (hasSum_one_div_deathRate_tail hk).tsum_eq

/-! ### The absorption martingale

K-G (5.11) observes that for a pure death process whose rates satisfy `Σ d_r⁻¹ < ∞`, the
function `φ_θ(x) = ∏_{r > x} (1 - θ d_r⁻¹)` makes `φ_θ(X_t) e^{θt}` a martingale, and that
`θ = 1` gives the clean closed form `φ₁(x) = (x-1)/(x+1)`.  The closed form is the whole
content that can be settled without the process, and it is settled here exactly: the finite
products have a closed form for every truncation, and the limit follows. -/

/-- `φ₁(x) = (x-1)/(x+1)`, the `θ = 1` absorption factor of K-G (5.11). -/
noncomputable def survivalFactor (x : ℕ) : ℝ := ((x : ℝ) - 1) / ((x : ℝ) + 1)

@[simp] theorem survivalFactor_one : survivalFactor 1 = 0 := by norm_num [survivalFactor]

@[simp] theorem survivalFactor_two : survivalFactor 2 = 1 / 3 := by
  norm_num [survivalFactor]

theorem survivalFactor_nonneg {x : ℕ} (hx : 1 ≤ x) : 0 ≤ survivalFactor x := by
  have hx' : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  unfold survivalFactor
  apply div_nonneg <;> linarith

theorem survivalFactor_lt_one (x : ℕ) : survivalFactor x < 1 := by
  have hx : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  unfold survivalFactor
  rw [div_lt_one (by linarith)]
  linarith

/-- **K-G (5.11), exactly, at every truncation.**  The product `∏_{r=x+1}^{x+m} (1 - d_r⁻¹)`
telescopes to a ratio of four linear factors.  The `θ = 1` factor `(x-1)/(x+1)` is the
`m → ∞` limit, and the correction `(x+m+1)/(x+m-1)` is exactly the finite-truncation error,
so no asymptotic argument is being hidden. -/
theorem survivalFactor_partialProd {x : ℕ} (hx : 2 ≤ x) (m : ℕ) :
    ∏ j ∈ Finset.range m, (1 - 1 / deathRate (x + 1 + j))
      = (((x : ℝ) - 1) * ((x : ℝ) + (m : ℝ) + 1))
          / (((x : ℝ) + 1) * ((x : ℝ) + (m : ℝ) - 1)) := by
  have hx' : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  induction m with
  | zero =>
      have h1 : ((x : ℝ) + 1) ≠ 0 := by linarith
      have h2 : ((x : ℝ) - 1) ≠ 0 := by linarith
      simp only [Finset.range_zero, Finset.prod_empty, Nat.cast_zero, add_zero]
      rw [mul_comm ((x : ℝ) + 1) ((x : ℝ) - 1), div_self (mul_ne_zero h2 h1)]
  | succ m ih =>
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have h1 : ((x : ℝ) + 1) ≠ 0 := by linarith
      have h2 : ((x : ℝ) + (m : ℝ) - 1) ≠ 0 := by linarith
      have h3 : ((x : ℝ) + (m : ℝ)) ≠ 0 := by linarith
      have h4 : ((x : ℝ) + (m : ℝ) + 1) ≠ 0 := by linarith
      have hd : deathRate (x + 1 + m) = ((x : ℝ) + (m : ℝ) + 1) * ((x : ℝ) + (m : ℝ)) / 2 := by
        unfold deathRate Descent.Core.pairCount
        push_cast
        ring
      have hfac : (1 : ℝ) - 1 / (((x : ℝ) + (m : ℝ) + 1) * ((x : ℝ) + (m : ℝ)) / 2)
          = (((x : ℝ) + (m : ℝ) - 1) * ((x : ℝ) + (m : ℝ) + 2))
              / (((x : ℝ) + (m : ℝ) + 1) * ((x : ℝ) + (m : ℝ))) := by
        rw [eq_div_iff (mul_ne_zero h4 h3)]
        field_simp
        ring
      rw [Finset.prod_range_succ, ih, hd, hfac, div_mul_div_comm]
      rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero h1 h2) (mul_ne_zero h4 h3))
        (mul_ne_zero h1 (by push_cast; intro hcon; exact h3 (by linarith)))]
      push_cast
      ring

/-- The truncated products, written so the tail correction is visible as an additive term. -/
theorem survivalFactor_partialProd_eq_mul {x : ℕ} (hx : 2 ≤ x) (m : ℕ) :
    ∏ j ∈ Finset.range m, (1 - 1 / deathRate (x + 1 + j))
      = survivalFactor x * (1 + 2 / ((x : ℝ) + (m : ℝ) - 1)) := by
  have hx' : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h1 : ((x : ℝ) + 1) ≠ 0 := by linarith
  have h2 : ((x : ℝ) + (m : ℝ) - 1) ≠ 0 := by linarith
  rw [survivalFactor_partialProd hx m]
  unfold survivalFactor
  field_simp
  ring

/-- **The infinite product of K-G (5.11) converges to `(x-1)/(x+1)`.** -/
theorem tendsto_survivalFactor_partialProd {x : ℕ} (hx : 2 ≤ x) :
    Tendsto (fun m : ℕ ↦ ∏ j ∈ Finset.range m, (1 - 1 / deathRate (x + 1 + j)))
      atTop (nhds (survivalFactor x)) := by
  have hx' : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hcorr : Tendsto (fun m : ℕ ↦ 1 + 2 / ((x : ℝ) + (m : ℝ) - 1)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add (tendsto_two_div_shift hx')
  simpa only [survivalFactor_partialProd_eq_mul hx, mul_one] using
    tendsto_const_nhds.mul hcorr

/-- **`inf_{x ≥ 2} φ₁(x) = 1/3`, and the infimum is attained at `x = 2`.**

This is the source of the constant `3` in K-G (5.13) and, through the supermartingale
argument K-G attributes to Kingman (1976), of the best-possible `3` in the Wright-Fisher
bound K-G (2.4).  The two threes are one theorem. -/
theorem one_le_three_mul_survivalFactor {x : ℕ} (hx : 2 ≤ x) : 1 ≤ 3 * survivalFactor x := by
  have hx' : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hpos : (0 : ℝ) < (x : ℝ) + 1 := by linarith
  have key : 3 * survivalFactor x - 1 = (2 * ((x : ℝ) - 2)) / ((x : ℝ) + 1) := by
    unfold survivalFactor
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ (2 * ((x : ℝ) - 2)) / ((x : ℝ) + 1) :=
    div_nonneg (by linarith) (by linarith)
  linarith

/-- The constant `3` is not improvable: at `x = 2` the inequality is an equality. -/
theorem three_mul_survivalFactor_two : 3 * survivalFactor 2 = 1 := by
  norm_num [survivalFactor]

/-- **K-G (5.13) as a Markov inequality.**  For ANY integer-valued random variable `K ≥ 1`,
the probability of `K ≥ 2` is at most three times the mean of `φ₁(K)`.  Applied to
`K = |R_t|` with the martingale identity K-G (5.12), `E φ₁(|R_t|) = ((n-1)/(n+1)) e^{-t}`,
this gives Kingman's `P{R_t ≠ Θ} ≤ 3 ((n-1)/(n+1)) e^{-t}`.

The hypothesis-free part is stated here and the martingale identity is not asserted: what
is proved is that the bound follows from the mean, by `one_le_three_mul_survivalFactor`
alone. -/
theorem measure_two_le_le_three_mul_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (K : Ω → ℕ) (hK : ∀ ω, 1 ≤ K ω)
    (hmeas : MeasurableSet {ω | 2 ≤ K ω})
    (hint : Integrable (fun ω ↦ survivalFactor (K ω)) μ) :
    (μ {ω | 2 ≤ K ω}).toReal ≤ 3 * ∫ ω, survivalFactor (K ω) ∂μ := by
  have hpt : ∀ ω, Set.indicator {ω | 2 ≤ K ω} (1 : Ω → ℝ) ω ≤ 3 * survivalFactor (K ω) := by
    intro ω
    rw [Set.indicator_apply]
    split_ifs with hω
    · simpa using one_le_three_mul_survivalFactor hω
    · linarith [survivalFactor_nonneg (hK ω)]
  have hmono : ∫ ω, Set.indicator {ω | 2 ≤ K ω} (1 : Ω → ℝ) ω ∂μ
      ≤ ∫ ω, 3 * survivalFactor (K ω) ∂μ :=
    integral_mono ((integrable_const (1 : ℝ)).indicator hmeas) (hint.const_mul 3) hpt
  rwa [integral_indicator_one hmeas, integral_const_mul] at hmono

/-! ### The transit-time density

K-C (5.9) gives the density of `T = Σ_{r≥2} τ_r` as the alternating series
`g(t) = Σ_{m≥2} (-1)^m ½ m(m-1)(2m-1) e^{-½ m(m-1) t}`, whose partial sums bound
`P{T_n > t}` uniformly in `n` (K-G (5.10)).  The series itself is not summed here; what is
recorded is its leading term, because that is what carries the constant. -/

/-- The `m`-th term of the transit-time density series, K-G (5.9), without its sign. -/
noncomputable def transitDensityTerm (m : ℕ) (t : ℝ) : ℝ :=
  deathRate m * (2 * (m : ℝ) - 1) * Real.exp (-(deathRate m * t))

/-- **The leading term is `3 e^{-t}`.**  The `m = 2` term of the K-G (5.9) density series is
exactly `3 e^{-t}`, which is the large-`t` asymptote of the uniform bound (5.10) -- and the
same `3` that `one_le_three_mul_survivalFactor` produces from the martingale side and that
K-G (2.4) reports as best possible for the Wright-Fisher model.  Three routes, one
constant. -/
theorem transitDensityTerm_two (t : ℝ) : transitDensityTerm 2 t = 3 * Real.exp (-t) := by
  unfold transitDensityTerm
  norm_num

/-- Below the first coalescence the series has nothing to say: the `m ≤ 1` terms vanish. -/
@[simp] theorem transitDensityTerm_one (t : ℝ) : transitDensityTerm 1 t = 0 := by
  simp [transitDensityTerm]

end Coalescent

end Descent
