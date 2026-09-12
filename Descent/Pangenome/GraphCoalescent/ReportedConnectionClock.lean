/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.TransitVariance
import Descent.Pangenome.GraphCoalescent.VisibleIntensityClock

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The reported connection clock: Laplace transform and moments, (D7)-(D9)

Section 6 of the hidden-lineage clock note reads the reported connection time off the ranked
history of the genealogy.  Let `B` be the number of true lineages right after the report first
connects, with law `p_b`.  The holding times `H_k ~ Exp(d_k)`, `d_k = C(k, 2)`, are independent of
the embedded jump chain, and given `B = b` the connection time is `τ_q = ∑_{k=b+1}^n H_k`.  So

  (D7) `E e^{-s τ_q} = ∑_b p_b ∏_{k=b+1}^n d_k / (s + d_k)`,
  (D8) `E τ_q = 2 ∑_b p_b / b - 2/n`,
  (D9) `E τ_q² = ∑_b p_b [(2/b - 2/n)² + ∑_{k=b+1}^n C(k, 2)^{-2}]`.

Everything special about the pangenome is in `p_b`; the rest is the Kingman ladder between `b` and
`n` lineages, and this file proves that part from the corpus ladder.

- `sum_one_div_deathRate_Ioc`: the telescoping `∑_{k=b+1}^n 1/C(k, 2) = 2/b - 2/n`, which is the
  conditional mean given `B = b`; `sum_one_div_deathRate_Ioc_eq_meanTransitTime_sub` reads it as
  the difference `E(T_n) - E(T_b)` of the corpus transit times of
  `Descent.Coalescent.Rates`.
- `sum_sq_one_div_deathRate_Ioc`: the conditional variance `∑_{k=b+1}^n C(k, 2)^{-2}` is the
  difference `Var(T_n) - Var(T_b)` of the corpus transit variances of
  `Descent.Coalescent.TransitVariance`.
- `kingmanLaplace_mul_prod_Ioc`: the conditional transform `∏_{k=b+1}^n d_k / (s + d_k)` is the
  factor that carries the Kingman transform `kingmanLaplace s b` of
  `Descent.Pangenome.GraphCoalescent.VisibleIntensityClock` up to `kingmanLaplace s n`.
- `sum_mul_sum_one_div_deathRate_Ioc`: (D8) for any first-connection law of total mass one on
  lineage counts `1 ≤ b ≤ n`.
- `sum_mul_secondMoment_eq`: (D9), the mixture of the conditional second moments
  `(∑ 1/d_k)² + ∑ 1/d_k²` in the closed form of the note.

Scope.  The file proves the ladder arithmetic of (D7)-(D9): the conditional mean, variance and
transform given `B = b`, and their mixture against a given law `p_b`.  The probabilistic step, that
independent exponential holding times give these conditional values and that mixing over an
independent `B` gives the unconditional ones, is not formalized here, and `p_b` itself is the
business of `RankedHistoryLaw`.

## Empirical status

None.  The bodies are identities between finite sums of the Kingman death rates, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.ReportedConnectionClock

open Coalescent Finset

/-! ## The Kingman ladder between `b` and `n` lineages -/

/-- The Kingman death rate is the pair count of the note, `d_k = C(k, 2)`. -/
theorem deathRate_eq_choose_two (k : ℕ) : deathRate k = (k.choose 2 : ℝ) := by
  unfold deathRate Descent.Core.pairCount
  rw [Nat.cast_choose_two]

/-- **(D8), the telescoping.**  Given `B = b`, the holding means of the phases
`k = b + 1, ..., n` add up to `∑_{k=b+1}^n 1/d_k = 2/b - 2/n`. -/
theorem sum_one_div_deathRate_Ioc {b n : ℕ} (hb : 1 ≤ b) (hbn : b ≤ n) :
    ∑ k ∈ Ioc b n, 1 / deathRate k = 2 / (b : ℝ) - 2 / (n : ℝ) := by
  induction n, hbn using Nat.le_induction with
  | base => simp
  | succ m hbm ih =>
    rw [sum_Ioc_succ_top hbm, ih, one_div_deathRate_eq (by omega : 2 ≤ m + 1)]
    have hcast : ((m + 1 : ℕ) : ℝ) - 1 = m := by
      push_cast
      ring
    rw [hcast]
    ring

/-- The telescoping in the binomial form of the note, `∑_{k=b+1}^n 1/C(k, 2) = 2/b - 2/n`. -/
theorem sum_one_div_choose_two_Ioc {b n : ℕ} (hb : 1 ≤ b) (hbn : b ≤ n) :
    ∑ k ∈ Ioc b n, 1 / ((k.choose 2 : ℕ) : ℝ) = 2 / (b : ℝ) - 2 / (n : ℝ) := by
  simp only [← deathRate_eq_choose_two]
  exact sum_one_div_deathRate_Ioc hb hbn

/-- The conditional mean given `B = b` is the difference of the corpus transit times,
`E(T_n) - E(T_b)`. -/
theorem sum_one_div_deathRate_Ioc_eq_meanTransitTime_sub {b n : ℕ} (hb : 1 ≤ b) (hbn : b ≤ n) :
    ∑ k ∈ Ioc b n, 1 / deathRate k = meanTransitTime n - meanTransitTime b := by
  rw [sum_one_div_deathRate_Ioc hb hbn, meanTransitTime_eq_two_sub (hb.trans hbn),
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
`k = b + 1, ..., n` add up to the difference `Var(T_n) - Var(T_b)` of the corpus transit
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

/-- **The conditional transform.**  Given `B = b`, the factor `∏_{k=b+1}^n d_k / (s + d_k)` of
(D7) carries the Kingman transform of `b` lineages up to that of `n`. -/
theorem kingmanLaplace_mul_prod_Ioc (s : ℝ) {b n : ℕ} (hb : 1 ≤ b) (hbn : b ≤ n) :
    kingmanLaplace s b * ∏ k ∈ Ioc b n, deathRate k / (s + deathRate k) = kingmanLaplace s n := by
  induction n, hbn using Nat.le_induction with
  | base => simp
  | succ m hbm ih =>
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (hb.trans hbm)
    rw [prod_Ioc_succ_top hbm, ← mul_assoc, ih]
    unfold kingmanLaplace
    rw [(by omega : 1 + j + 1 - 1 = j + 1), (by omega : 1 + j - 1 = j), prod_range_succ,
      (by omega : j + 2 = 1 + j + 1), add_comm s]

/-! ## Mixing over the first-connection law -/

/-- **(D8).**  If the first-connection law `p` has total mass one on lineage counts `1 ≤ b ≤ n`,
mixing the conditional means gives `E τ_q = 2 ∑_b p_b / b - 2/n`. -/
theorem sum_mul_sum_one_div_deathRate_Ioc {n : ℕ} {S : Finset ℕ} (p : ℕ → ℝ)
    (hS : ∀ b ∈ S, 1 ≤ b ∧ b ≤ n) (hp : ∑ b ∈ S, p b = 1) :
    ∑ b ∈ S, p b * ∑ k ∈ Ioc b n, 1 / deathRate k =
      2 * ∑ b ∈ S, p b / (b : ℝ) - 2 / (n : ℝ) := by
  have hterm : ∀ b ∈ S, p b * ∑ k ∈ Ioc b n, 1 / deathRate k =
      2 * (p b / (b : ℝ)) - p b * (2 / (n : ℝ)) := fun b hb ↦ by
    rw [sum_one_div_deathRate_Ioc (hS b hb).1 (hS b hb).2]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hp,
    one_mul]

/-- **(D9).**  Given `B = b` the second moment of `τ_q` is its squared mean plus its variance,
`(∑ 1/d_k)² + ∑ 1/d_k²`; mixing over `p` gives
`E τ_q² = ∑_b p_b [(2/b - 2/n)² + (Var(T_n) - Var(T_b))]`, and
`Var(T_n) - Var(T_b) = ∑_{k=b+1}^n C(k, 2)^{-2}` by `sum_one_div_choose_two_sq_Ioc`. -/
theorem sum_mul_secondMoment_eq {n : ℕ} {S : Finset ℕ} (p : ℕ → ℝ)
    (hS : ∀ b ∈ S, 1 ≤ b ∧ b ≤ n) :
    ∑ b ∈ S, p b * ((∑ k ∈ Ioc b n, 1 / deathRate k) ^ 2 +
        ∑ k ∈ Ioc b n, (1 / deathRate k) ^ 2) =
      ∑ b ∈ S, p b * ((2 / (b : ℝ) - 2 / (n : ℝ)) ^ 2 + (varTransitTime n - varTransitTime b)) := by
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  rw [sum_one_div_deathRate_Ioc (hS b hb).1 (hS b hb).2,
    sum_sq_one_div_deathRate_Ioc (hS b hb).1 (hS b hb).2]

end Descent.Pangenome.GraphCoalescent.ReportedConnectionClock
