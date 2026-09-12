/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.TransitVariance
import Descent.Pangenome.GraphCoalescent.ReportedConnectionClock
import Descent.Pangenome.GraphCoalescent.VisibleIntensityClock

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The Kingman ladder under the reported connection clock

`Descent.Pangenome.GraphCoalescent.ReportedConnectionClock` proves (D7)-(D9) of the hidden-lineage
clock note on the product of a jump-chain trajectory and an independent Kingman clock.  Given that
the report first connects with `B = b` true lineages, the connection time is the sum of the
holding times of the phases `k = b + 1, …, n`, so its conditional mean, variance and transform are
sums and products over the Kingman ladder between `b` and `n` lineages.  This file identifies
those ladder sums with the corpus quantities of the whole Kingman transit.

- `sum_Ioc_one_div_deathRate_eq_meanTransitTime_sub`: the conditional mean `∑_{k=b+1}^n 1/d_k` is
  `E(T_n) - E(T_b)`, the difference of the corpus transit times of `Descent.Coalescent.Rates`.
- `sum_sq_one_div_deathRate_Ioc`: the conditional variance `∑_{k=b+1}^n 1/d_k²` is
  `Var(T_n) - Var(T_b)`, the difference of the corpus transit variances of
  `Descent.Coalescent.TransitVariance`.
- `kingmanLaplace_mul_prod_Ioc`: the conditional transform `∏_{k=b+1}^n d_k/(d_k + θ)` carries the
  Kingman transform `kingmanLaplace θ b` of
  `Descent.Pangenome.GraphCoalescent.VisibleIntensityClock` up to `kingmanLaplace θ n`, and
  `prod_Ioc_eq_kingmanLaplace_div` is its quotient form.
- `deathRate_eq_choose_two`, `sum_one_div_choose_two_Ioc`, `sum_one_div_choose_two_sq_Ioc`: the
  binomial forms `d_k = C(k, 2)`, `∑ 1/C(k, 2) = 2/b - 2/n` and `∑ C(k, 2)^{-2}` of the note.
- `connectionTime_laplace_eq_kingmanLaplace`, `connectionTime_mean_eq_meanTransitTime`,
  `connectionTime_secondMoment_eq_varTransitTime`: (D7), (D8) and (D9) of
  `ReportedConnectionClock` read through these identifications,
  `E e^{-θ τ_q} = ∑_b p_b L_n(θ)/L_b(θ)`, `E τ_q = ∑_b p_b (E(T_n) - E(T_b))` and
  `E τ_q² = ∑_b p_b [(2/b - 2/n)² + (Var(T_n) - Var(T_b))]`.

Scope.  The probabilistic content, that independent exponential holding times and an independent
stopping level give (D7)-(D9), is proved in `ReportedConnectionClock`; this file adds only the
identities between ladder sums and the corpus transit quantities.

## Empirical status

None.  The bodies are identities between finite sums and products of the Kingman death rates, so
no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.ReportedConnectionLadder

open Coalescent Finset MeasureTheory

/-! ## The Kingman ladder between `b` and `n` lineages -/

/-- The Kingman death rate is the pair count of the note, `d_k = C(k, 2)`. -/
theorem deathRate_eq_choose_two (k : ℕ) : deathRate k = (k.choose 2 : ℝ) := by
  unfold deathRate Descent.Core.pairCount
  rw [Nat.cast_choose_two]

/-- The telescoping in the binomial form of the note, `∑_{k=b+1}^n 1/C(k, 2) = 2/b - 2/n`. -/
theorem sum_one_div_choose_two_Ioc {b n : ℕ} (hb : 1 ≤ b) (hbn : b ≤ n) :
    ∑ k ∈ Ioc b n, 1 / ((k.choose 2 : ℕ) : ℝ) = 2 / (b : ℝ) - 2 / (n : ℝ) := by
  simp only [← deathRate_eq_choose_two]
  exact sum_Ioc_one_div_deathRate hb hbn

/-- **The conditional mean.**  Given `B = b`, the holding means of the phases `k = b + 1, …, n`
add up to the difference `E(T_n) - E(T_b)` of the corpus transit times. -/
theorem sum_Ioc_one_div_deathRate_eq_meanTransitTime_sub {b n : ℕ} (hb : 1 ≤ b) (hbn : b ≤ n) :
    ∑ k ∈ Ioc b n, 1 / deathRate k = meanTransitTime n - meanTransitTime b := by
  rw [sum_Ioc_one_div_deathRate hb hbn, meanTransitTime_eq_two_sub (hb.trans hbn),
    meanTransitTime_eq_two_sub hb]
  ring

/-- One more lineage adds one squared holding mean to the corpus transit variance. -/
theorem varTransitTime_succ {m : ℕ} (hm : 1 ≤ m) :
    varTransitTime (m + 1) = varTransitTime m + (1 / deathRate (m + 1)) ^ 2 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
  unfold varTransitTime
  rw [(by omega : 1 + j + 1 - 1 = j + 1), (by omega : 1 + j - 1 = j), sum_range_succ,
    (by omega : j + 2 = 1 + j + 1)]

/-- **The conditional variance.**  Given `B = b`, the holding variances of the phases
`k = b + 1, …, n` add up to the difference `Var(T_n) - Var(T_b)` of the corpus transit
variances. -/
theorem sum_sq_one_div_deathRate_Ioc {b n : ℕ} (hb : 1 ≤ b) (hbn : b ≤ n) :
    ∑ k ∈ Ioc b n, (1 / deathRate k) ^ 2 = varTransitTime n - varTransitTime b := by
  induction n, hbn using Nat.le_induction with
  | base => simp
  | succ m hbm ih =>
    rw [sum_Ioc_succ_top hbm, ih, varTransitTime_succ (hb.trans hbm)]
    ring

/-- The conditional variance in the binomial form of the note, `∑_{k=b+1}^n C(k, 2)^{-2}`. -/
theorem sum_one_div_choose_two_sq_Ioc {b n : ℕ} (hb : 1 ≤ b) (hbn : b ≤ n) :
    ∑ k ∈ Ioc b n, 1 / ((k.choose 2 : ℕ) : ℝ) ^ 2 = varTransitTime n - varTransitTime b := by
  simp only [← deathRate_eq_choose_two, ← one_div_pow]
  exact sum_sq_one_div_deathRate_Ioc hb hbn

/-- **The conditional transform.**  Given `B = b`, the factor `∏_{k=b+1}^n d_k/(d_k + θ)` carries
the Kingman transform of `b` lineages up to that of `n`. -/
theorem kingmanLaplace_mul_prod_Ioc (θ : ℝ) {b n : ℕ} (hb : 1 ≤ b) (hbn : b ≤ n) :
    kingmanLaplace θ b * ∏ k ∈ Ioc b n, deathRate k / (deathRate k + θ) = kingmanLaplace θ n := by
  induction n, hbn using Nat.le_induction with
  | base => simp
  | succ m hbm ih =>
    rw [prod_Ioc_succ_top hbm, ← mul_assoc, ih, kingmanLaplace_succ θ (hb.trans hbm)]

/-- The Kingman transform at a nonnegative argument is positive. -/
theorem kingmanLaplace_pos {θ : ℝ} (hθ : 0 ≤ θ) (m : ℕ) : 0 < kingmanLaplace θ m :=
  prod_pos fun k _ ↦ div_pos (deathRate_add_two_pos k)
    (add_pos_of_pos_of_nonneg (deathRate_add_two_pos k) hθ)

/-- The conditional transform as a quotient of Kingman transforms, `L_n(θ)/L_b(θ)`. -/
theorem prod_Ioc_eq_kingmanLaplace_div {θ : ℝ} (hθ : 0 ≤ θ) {b n : ℕ} (hb : 1 ≤ b)
    (hbn : b ≤ n) :
    ∏ k ∈ Ioc b n, deathRate k / (deathRate k + θ) = kingmanLaplace θ n / kingmanLaplace θ b := by
  have h := kingmanLaplace_mul_prod_Ioc θ hb hbn
  rw [eq_div_iff (kingmanLaplace_pos hθ b).ne', ← h]
  ring

/-! ## (D7)-(D9) through the ladder -/

/-- **(D7) through the Kingman transform**: `E e^{-θ τ_q} = ∑_b p_b L_n(θ)/L_b(θ)`. -/
theorem connectionTime_laplace_eq_kingmanLaplace {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    ∫⁻ p, ENNReal.ofReal (Real.exp (-(θ * connectionTime s p))) ∂(trajectoryClockLaw n)
      = ENNReal.ofReal (∑ b ∈ Icc 1 n,
          stoppingProb s b * (kingmanLaplace θ n / kingmanLaplace θ b)) := by
  rw [connectionTime_laplace hn s hθ]
  congr 1
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  rw [prod_Ioc_eq_kingmanLaplace_div hθ (mem_Icc.mp hb).1 (mem_Icc.mp hb).2]

/-- **(D8) through the transit times**: `E τ_q = ∑_b p_b (E(T_n) - E(T_b))`. -/
theorem connectionTime_mean_eq_meanTransitTime {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    ∫⁻ p, ENNReal.ofReal (connectionTime s p) ∂(trajectoryClockLaw n)
      = ENNReal.ofReal (∑ b ∈ Icc 1 n,
          stoppingProb s b * (meanTransitTime n - meanTransitTime b)) := by
  rw [connectionTime_mean hn s]
  congr 1
  have hterm : ∀ b ∈ Icc 1 n, stoppingProb s b * (meanTransitTime n - meanTransitTime b)
      = 2 * (stoppingProb s b / b) - 2 / n * stoppingProb s b := fun b hb ↦ by
    rw [← sum_Ioc_one_div_deathRate_eq_meanTransitTime_sub (mem_Icc.mp hb).1 (mem_Icc.mp hb).2,
      sum_Ioc_one_div_deathRate (mem_Icc.mp hb).1 (mem_Icc.mp hb).2]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_stoppingProb hn s, mul_one]

/-- **(D9) through the transit variances**:
`E τ_q² = ∑_b p_b [(2/b - 2/n)² + (Var(T_n) - Var(T_b))]`. -/
theorem connectionTime_secondMoment_eq_varTransitTime {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    ∫⁻ p, ENNReal.ofReal (connectionTime s p ^ 2) ∂(trajectoryClockLaw n)
      = ENNReal.ofReal (∑ b ∈ Icc 1 n, stoppingProb s b *
          ((2 / (b : ℝ) - 2 / n) ^ 2 + (varTransitTime n - varTransitTime b))) := by
  rw [connectionTime_secondMoment hn s]
  congr 1
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  rw [sum_sq_one_div_deathRate_Ioc (mem_Icc.mp hb).1 (mem_Icc.mp hb).2]

end Descent.Pangenome.GraphCoalescent.ReportedConnectionLadder
