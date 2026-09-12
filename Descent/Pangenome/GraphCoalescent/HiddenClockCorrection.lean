/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.HiddenLoadFiltering
import Descent.Pangenome.GraphCoalescent.ReportedConnectionFirstStep

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Correcting the apparent coalescence clock of a compressed pangenome

A graph built at interface `s` compresses the panel's `n` haplotypes into `w = Linkage.width s`
graph states. Read as a Kingman coalescent of its own `w` lineages, the graph predicts the time to
common ancestry `2 - 2/w`. What it reports is the connection time `τ_q` of the observed genealogy,
whose mean is no larger (Theorem C), while the panel's own time to common ancestry `T_n` has mean
`2 - 2/n`, no smaller. This module gives the exact correction between the three clocks, the hidden
quantity the correction rests on, and the error of the corrected clock.

## The hidden load at connection

`B = stoppingLevel s` is the number of true lineages right after the report first connects: the
total hidden load of the one remaining component. On every path of `trajectoryClockLaw n` the
panel clock splits into the connection time and the residual time during which the `B` hidden
lineages coalesce unseen (`panelTime_eq_connectionTime_add_residualTime`). Mixing the Kingman
clock over `p_b = Pr(B = b)` (`lintegral_stoppingMix`) gives the moments, with
`v_m = varTransitTime m = Σ_{k=2}^{m} d_k⁻²`:

* `lintegral_panelTime`, `lintegral_sq_panelTime`: `E T_n = 2 - 2/n`, `E T_n² = (2 - 2/n)² + v_n`.
* `lintegral_residualTime`, `lintegral_sq_residualTime`: `E R = Σ_b p_b (2 - 2/b)` and
  `E R² = Σ_b p_b ((2 - 2/b)² + v_b)`.
* `lintegral_inv_stoppingLevel`, `lintegral_stoppingLevel`: `E[1/B] = Σ_b p_b/b`, `E B = Σ_b p_b b`.
* `lintegral_connectionTime_mul_panelTime`:
  `E[τ_q T_n] = Σ_b p_b ((2/b - 2/n)(2 - 2/n) + v_n - v_b)`.

**The first moment of the connection clock identifies the harmonic mean of the hidden load at
connection**: `E[1/B] = E τ_q/2 + 1/n` (`inv_stoppingLevel_mean_eq`). So the connected report
hides, in expectation, at least `2n/(n E τ_q + 2)` lineages (`two_mul_div_le_mean_stoppingLevel`,
through `one_le_mean_mul_mean_inv`).

## The corrected clock and its error

* `residualTime_mean_eq`: `E R = 2 - 2/n - E τ_q`, and `panelTime_mean_eq_add`:
  `E T_n = E τ_q + E R`.
  The corrected clock `T̂ = τ_q + (2 - 2/n - E τ_q)` is therefore an unbiased predictor of `T_n`,
  and its error `T_n - T̂ = R - E R` has mean square `Var R`.
* `variance_residualTime_eq`: `Var R = Σ_b p_b v_b + 4 Var(1/B)`, the hidden coalescent variance
  below the connection plus the spread of the hidden load.
* `covariance_connectionTime_panelTime`: `Cov(τ_q, T_n) = Σ_b p_b (v_n - v_b)`, the variance of
  the holding times the report sees.
* `connectionTime_mean_le_two_sub`: the compressed Kingman clock overstates the connection clock,
  `E τ_q ≤ 2 - 2/w`, and `panelTime_mean_sub_two_sub`: it understates the panel clock by
  `2/w - 2/n`.

## The observed intensity at the start

Started from the fiber sizes `c`, the observed intensity of a visible merger of `C` and `D` is
`c_C c_D` (`observedIntensity_pointPrior`, from
`HiddenLoadFiltering.observedIntensity_eq_posteriorMean`), and the report's hazard at the start is
`e₂(c) = C(n, 2) - Σ_i C(c_i, 2)` (`loadVisibleIntensity_eq_choose_sub`); with two fibers it is
`c₁ c₂` (`loadVisibleIntensity_fin_two`).

Scope. The expectations are lower Lebesgue integrals of `ENNReal.ofReal` of nonnegative times on
the product of the jump chain and the exponential clock, as in `ReportedConnectionClock`, and the
moments of `B` are finite sums over `p_b = F_b - F_{b+1}` (`stoppingProb_eq`). The estimation of
`E τ_q` from data across loci, the conditional law of `T_n` given `τ_q`, and closed forms of `p_b`
at particular fiber sizes are not in this module.

## Empirical status

None. The bodies here are integrals over the corpus Kingman path law and finite sums over the law
of the stopping level; whether a real genealogy is Kingman's, and whether a real graph's interface
is fixed independently of it, are the modelling premises of those modules.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.HiddenClockCorrection

open Finset Coalescent MeasureTheory
open scoped Classical ENNReal

noncomputable section

/-! ### The three clocks on one path -/

/-- **The panel's time to its most recent common ancestor**: the holding times at every level.

Empirical status: NOT AN EMPIRICAL CLAIM.  A sum of coordinates of the path. -/
def panelTime (n : ℕ) (p : List (ER n) × (ℕ → ℝ)) : ℝ :=
  ∑ j ∈ Ico 0 (n - 1), p.2 j

/-- **The residual time after the report connects**: the holding times at the levels `2, …, B`,
while the `B` hidden lineages of the connected report coalesce unseen.

Empirical status: NOT AN EMPIRICAL CLAIM.  A sum of coordinates of the path. -/
def residualTime {n : ℕ} (s : Fin n → Fin n) (p : List (ER n) × (ℕ → ℝ)) : ℝ :=
  ∑ j ∈ Ico 0 (stoppingLevel s p.1 - 1), p.2 j

/-- **The panel clock splits at the connection**: `T_n = τ_q + R` on every path. -/
theorem panelTime_eq_connectionTime_add_residualTime {n : ℕ} (s : Fin n → Fin n)
    (p : List (ER n) × (ℕ → ℝ)) :
    panelTime n p = connectionTime s p + residualTime s p := by
  have hB : stoppingLevel s p.1 - 1 ≤ n - 1 :=
    Nat.sub_le_sub_right (Nat.findGreatest_le n) 1
  rw [panelTime, connectionTime, residualTime,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le (stoppingLevel s p.1 - 1)) hB, add_comm]

/-! ### Blocks of holding times -/

theorem one_div_deathRate_nonneg (j : ℕ) : 0 ≤ 1 / deathRate (j + 2) :=
  (one_div_pos.mpr (deathRate_add_two_pos j)).le

theorem two_sub_two_div_nonneg {b : ℕ} (hb : 1 ≤ b) : 0 ≤ 2 - 2 / (b : ℝ) := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  exact sub_nonneg.mpr (div_le_self (by norm_num) hb1)

theorem measurable_sum_coords (T : Finset ℕ) : Measurable fun ω : ℕ → ℝ ↦ ∑ j ∈ T, ω j :=
  Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j

theorem lintegral_const_ofReal (x : ℝ) :
    ∫⁻ _ : ℕ → ℝ, ENNReal.ofReal x ∂kingmanClock = ENNReal.ofReal x := by
  rw [lintegral_const, measure_univ, mul_one]

/-- The mean of the holding times above level `b`: `2/b - 2/n`. -/
theorem sum_Ico_pred_one_div_deathRate {b n : ℕ} (hb : 1 ≤ b) (hbn : b ≤ n) :
    ∑ j ∈ Ico (b - 1) (n - 1), 1 / deathRate (j + 2) = 2 / (b : ℝ) - 2 / n := by
  rw [sum_Ico_eq_sub _ (by omega)]
  show meanTransitTime n - meanTransitTime b = _
  rw [meanTransitTime_eq_two_sub (show 1 ≤ n by omega), meanTransitTime_eq_two_sub hb]
  ring

/-- The variance of the holding times above level `b`: `v_n - v_b`. -/
theorem sum_Ico_pred_sq_one_div_deathRate {b n : ℕ} (hbn : b ≤ n) :
    ∑ j ∈ Ico (b - 1) (n - 1), (1 / deathRate (j + 2)) ^ 2
      = varTransitTime n - varTransitTime b := by
  rw [sum_Ico_eq_sub _ (by omega)]
  rfl

/-- The mean of the holding times below level `b`: `2 - 2/b`. -/
theorem lintegral_sum_Ico_zero {b : ℕ} (hb : 1 ≤ b) :
    ∫⁻ ω, ENNReal.ofReal (∑ j ∈ Ico 0 (b - 1), ω j) ∂kingmanClock
      = ENNReal.ofReal (2 - 2 / (b : ℝ)) := by
  rw [lintegral_sum_kingmanClock, ← range_eq_Ico]
  exact congrArg ENNReal.ofReal (meanTransitTime_eq_two_sub hb)

/-- The second moment of the holding times below level `b`: `(2 - 2/b)² + v_b`. -/
theorem lintegral_sq_sum_Ico_zero {b : ℕ} (hb : 1 ≤ b) :
    ∫⁻ ω, ENNReal.ofReal ((∑ j ∈ Ico 0 (b - 1), ω j) ^ 2) ∂kingmanClock
      = ENNReal.ofReal ((2 - 2 / (b : ℝ)) ^ 2 + varTransitTime b) := by
  rw [lintegral_sq_sum_kingmanClock, ← range_eq_Ico, ← meanTransitTime_eq_two_sub hb]
  rfl

/-- **The product of two disjoint blocks of holding times** integrates to the product of their
means. -/
theorem lintegral_mul_sum_kingmanClock {A B : Finset ℕ} (hAB : Disjoint A B) :
    ∫⁻ ω, ENNReal.ofReal ((∑ j ∈ A, ω j) * ∑ j ∈ B, ω j) ∂kingmanClock
      = ENNReal.ofReal ((∑ j ∈ A, 1 / deathRate (j + 2)) * ∑ j ∈ B, 1 / deathRate (j + 2)) := by
  have hae : (fun ω : ℕ → ℝ ↦ ENNReal.ofReal ((∑ j ∈ A, ω j) * ∑ j ∈ B, ω j))
      =ᵐ[kingmanClock] fun ω ↦ ∑ i ∈ A, ∑ j ∈ B, ENNReal.ofReal (ω i) * ENNReal.ofReal (ω j) := by
    filter_upwards [ae_nonneg_kingmanClock] with ω hω
    rw [ENNReal.ofReal_mul (sum_nonneg fun j _ ↦ hω j),
      ENNReal.ofReal_sum_of_nonneg fun j _ ↦ hω j, ENNReal.ofReal_sum_of_nonneg fun j _ ↦ hω j,
      sum_mul_sum]
  rw [lintegral_congr_ae hae,
    lintegral_finset_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦
      (measurable_pi_apply i).ennreal_ofReal.mul (measurable_pi_apply j).ennreal_ofReal,
    ENNReal.ofReal_mul (sum_nonneg fun j _ ↦ one_div_deathRate_nonneg j),
    ENNReal.ofReal_sum_of_nonneg fun j _ ↦ one_div_deathRate_nonneg j,
    ENNReal.ofReal_sum_of_nonneg fun j _ ↦ one_div_deathRate_nonneg j, sum_mul_sum]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [lintegral_finset_sum _ fun j _ ↦
    (measurable_pi_apply i).ennreal_ofReal.mul (measurable_pi_apply j).ennreal_ofReal]
  refine sum_congr rfl fun j hj ↦ ?_
  exact lintegral_mul_coords_kingmanClock fun h ↦ Finset.disjoint_left.mp hAB hi (h ▸ hj)

/-- **A block of holding times against all the holding times below its top**: with
`A = Σ_{Ico m k}` and `T = Σ_{Ico 0 k}`, `E[A T] = E A · E T + Σ_{Ico m k} d⁻²`. -/
theorem lintegral_block_mul_total {m k : ℕ} (hmk : m ≤ k) :
    ∫⁻ ω, ENNReal.ofReal ((∑ j ∈ Ico m k, ω j) * ∑ j ∈ Ico 0 k, ω j) ∂kingmanClock
      = ENNReal.ofReal ((∑ j ∈ Ico m k, 1 / deathRate (j + 2))
          * ∑ j ∈ Ico 0 k, 1 / deathRate (j + 2)
        + ∑ j ∈ Ico m k, (1 / deathRate (j + 2)) ^ 2) := by
  have hsplit : ∀ f : ℕ → ℝ, ∑ j ∈ Ico 0 k, f j = ∑ j ∈ Ico 0 m, f j + ∑ j ∈ Ico m k, f j :=
    fun f ↦ (sum_Ico_consecutive f (Nat.zero_le m) hmk).symm
  have hae : (fun ω : ℕ → ℝ ↦ ENNReal.ofReal ((∑ j ∈ Ico m k, ω j) * ∑ j ∈ Ico 0 k, ω j))
      =ᵐ[kingmanClock] fun ω ↦ ENNReal.ofReal ((∑ j ∈ Ico m k, ω j) * ∑ j ∈ Ico 0 m, ω j)
        + ENNReal.ofReal ((∑ j ∈ Ico m k, ω j) ^ 2) := by
    filter_upwards [ae_nonneg_kingmanClock] with ω hω
    have hA : 0 ≤ ∑ j ∈ Ico m k, ω j := sum_nonneg fun j _ ↦ hω j
    have hB : 0 ≤ ∑ j ∈ Ico 0 m, ω j := sum_nonneg fun j _ ↦ hω j
    rw [hsplit, ← ENNReal.ofReal_add (mul_nonneg hA hB) (sq_nonneg _)]
    congr 1
    ring
  have h1 : 0 ≤ (∑ j ∈ Ico m k, 1 / deathRate (j + 2)) * ∑ j ∈ Ico 0 m, 1 / deathRate (j + 2) :=
    mul_nonneg (sum_nonneg fun j _ ↦ one_div_deathRate_nonneg j)
      (sum_nonneg fun j _ ↦ one_div_deathRate_nonneg j)
  have h2 : 0 ≤ (∑ j ∈ Ico m k, 1 / deathRate (j + 2)) ^ 2
      + ∑ j ∈ Ico m k, (1 / deathRate (j + 2)) ^ 2 :=
    add_nonneg (sq_nonneg _) (sum_nonneg fun j _ ↦ sq_nonneg _)
  rw [lintegral_congr_ae hae,
    lintegral_add_left ((measurable_sum_coords _).mul (measurable_sum_coords _)).ennreal_ofReal,
    lintegral_mul_sum_kingmanClock (Ico_disjoint_Ico_consecutive 0 m k).symm,
    lintegral_sq_sum_kingmanClock, ← ENNReal.ofReal_add h1 h2, hsplit]
  congr 1
  ring

/-- The connection block against the whole clock, at a stopping level `b`. -/
theorem lintegral_connectionBlock_mul_panel {b n : ℕ} (hb : 1 ≤ b) (hbn : b ≤ n) :
    ∫⁻ ω, ENNReal.ofReal ((∑ j ∈ Ico (b - 1) (n - 1), ω j) * ∑ j ∈ Ico 0 (n - 1), ω j)
        ∂kingmanClock
      = ENNReal.ofReal ((2 / (b : ℝ) - 2 / n) * (2 - 2 / (n : ℝ))
          + (varTransitTime n - varTransitTime b)) := by
  rw [lintegral_block_mul_total (by omega : b - 1 ≤ n - 1),
    sum_Ico_pred_one_div_deathRate hb hbn, sum_Ico_pred_sq_one_div_deathRate hbn,
    ← range_eq_Ico, ← meanTransitTime_eq_two_sub (show 1 ≤ n by omega)]
  rfl

theorem cross_value_nonneg {b n : ℕ} (hb : 1 ≤ b) (hbn : b ≤ n) :
    0 ≤ (2 / (b : ℝ) - 2 / n) * (2 - 2 / (n : ℝ)) + (varTransitTime n - varTransitTime b) := by
  rw [← sum_Ico_pred_one_div_deathRate hb hbn, ← sum_Ico_pred_sq_one_div_deathRate hbn]
  exact add_nonneg (mul_nonneg (sum_nonneg fun k _ ↦ one_div_deathRate_nonneg k)
    (two_sub_two_div_nonneg (show 1 ≤ n by omega))) (sum_nonneg fun k _ ↦ sq_nonneg _)

/-! ### Mixing over the stopping level -/

/-- **Mixing over the stopping level.** A functional of `B` and the clock, whose clock integral at
level `b` is `g b`, integrates to `Σ_b p_b g b`. -/
theorem lintegral_stoppingMix {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n)
    (G : ℕ → (ℕ → ℝ) → ℝ) (hG : ∀ b, Measurable (G b)) (g : ℕ → ℝ)
    (hg : ∀ b ∈ Icc 1 n, 0 ≤ g b)
    (hGg : ∀ b ∈ Icc 1 n, ∫⁻ ω, ENNReal.ofReal (G b ω) ∂kingmanClock = ENNReal.ofReal (g b)) :
    ∫⁻ p, ENNReal.ofReal (G (stoppingLevel s p.1) p.2) ∂(trajectoryClockLaw n)
      = ENNReal.ofReal (∑ b ∈ Icc 1 n, stoppingProb s b * g b) := by
  refine (lintegral_trajectoryClockLaw hn s (fun b ω ↦ ENNReal.ofReal (G b ω))
    fun b ↦ (hG b).ennreal_ofReal).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun b hb ↦ mul_nonneg ENNReal.toReal_nonneg (hg b hb)]
  refine sum_congr rfl fun b hb ↦ ?_
  rw [hGg b hb, stoppingProb, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]

/-- **The panel clock**: `E T_n = 2 - 2/n`. -/
theorem lintegral_panelTime {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    ∫⁻ p, ENNReal.ofReal (panelTime n p) ∂(trajectoryClockLaw n)
      = ENNReal.ofReal (2 - 2 / (n : ℝ)) := by
  have h := lintegral_stoppingMix hn s (fun _ ω ↦ ∑ j ∈ Ico 0 (n - 1), ω j)
    (fun _ ↦ measurable_sum_coords _) (fun _ ↦ 2 - 2 / (n : ℝ))
    (fun _ _ ↦ two_sub_two_div_nonneg (show 1 ≤ n by omega))
    (fun _ _ ↦ lintegral_sum_Ico_zero (show 1 ≤ n by omega))
  rw [← sum_mul, sum_stoppingProb hn s, one_mul] at h
  exact h

/-- **The second moment of the panel clock**: `E T_n² = (2 - 2/n)² + v_n`. -/
theorem lintegral_sq_panelTime {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    ∫⁻ p, ENNReal.ofReal (panelTime n p ^ 2) ∂(trajectoryClockLaw n)
      = ENNReal.ofReal ((2 - 2 / (n : ℝ)) ^ 2 + varTransitTime n) := by
  have h := lintegral_stoppingMix hn s (fun _ ω ↦ (∑ j ∈ Ico 0 (n - 1), ω j) ^ 2)
    (fun _ ↦ (measurable_sum_coords _).pow_const 2)
    (fun _ ↦ (2 - 2 / (n : ℝ)) ^ 2 + varTransitTime n)
    (fun _ _ ↦ add_nonneg (sq_nonneg _) (sum_nonneg fun k _ ↦ sq_nonneg _))
    (fun _ _ ↦ lintegral_sq_sum_Ico_zero (show 1 ≤ n by omega))
  rw [← sum_mul, sum_stoppingProb hn s, one_mul] at h
  exact h

/-- **The residual clock**: `E R = Σ_b p_b (2 - 2/b)`. -/
theorem lintegral_residualTime {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    ∫⁻ p, ENNReal.ofReal (residualTime s p) ∂(trajectoryClockLaw n)
      = ENNReal.ofReal (∑ b ∈ Icc 1 n, stoppingProb s b * (2 - 2 / (b : ℝ))) :=
  lintegral_stoppingMix hn s (fun b ω ↦ ∑ j ∈ Ico 0 (b - 1), ω j)
    (fun _ ↦ measurable_sum_coords _) (fun b ↦ 2 - 2 / (b : ℝ))
    (fun _ hb ↦ two_sub_two_div_nonneg (mem_Icc.mp hb).1)
    (fun _ hb ↦ lintegral_sum_Ico_zero (mem_Icc.mp hb).1)

/-- **The second moment of the residual clock**: `E R² = Σ_b p_b ((2 - 2/b)² + v_b)`. -/
theorem lintegral_sq_residualTime {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    ∫⁻ p, ENNReal.ofReal (residualTime s p ^ 2) ∂(trajectoryClockLaw n)
      = ENNReal.ofReal (∑ b ∈ Icc 1 n,
          stoppingProb s b * ((2 - 2 / (b : ℝ)) ^ 2 + varTransitTime b)) :=
  lintegral_stoppingMix hn s (fun b ω ↦ (∑ j ∈ Ico 0 (b - 1), ω j) ^ 2)
    (fun _ ↦ (measurable_sum_coords _).pow_const 2)
    (fun b ↦ (2 - 2 / (b : ℝ)) ^ 2 + varTransitTime b)
    (fun _ _ ↦ add_nonneg (sq_nonneg _) (sum_nonneg fun k _ ↦ sq_nonneg _))
    (fun _ hb ↦ lintegral_sq_sum_Ico_zero (mem_Icc.mp hb).1)

/-- **The inverse hidden load at connection**: `E[1/B] = Σ_b p_b/b`. -/
theorem lintegral_inv_stoppingLevel {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    ∫⁻ p, ENNReal.ofReal (1 / (stoppingLevel s p.1 : ℝ)) ∂(trajectoryClockLaw n)
      = ENNReal.ofReal (∑ b ∈ Icc 1 n, stoppingProb s b * (1 / (b : ℝ))) :=
  lintegral_stoppingMix hn s (fun b _ ↦ 1 / (b : ℝ)) (fun _ ↦ measurable_const)
    (fun b ↦ 1 / (b : ℝ)) (fun b _ ↦ one_div_nonneg.mpr (Nat.cast_nonneg b))
    (fun b _ ↦ lintegral_const_ofReal (1 / (b : ℝ)))

/-- **The hidden load at connection**: `E B = Σ_b p_b b`. -/
theorem lintegral_stoppingLevel {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    ∫⁻ p, ENNReal.ofReal (stoppingLevel s p.1 : ℝ) ∂(trajectoryClockLaw n)
      = ENNReal.ofReal (∑ b ∈ Icc 1 n, stoppingProb s b * (b : ℝ)) :=
  lintegral_stoppingMix hn s (fun b _ ↦ (b : ℝ)) (fun _ ↦ measurable_const) (fun b ↦ (b : ℝ))
    (fun b _ ↦ Nat.cast_nonneg b) (fun b _ ↦ lintegral_const_ofReal (b : ℝ))

/-- **The connection clock against the panel clock**:
`E[τ_q T_n] = Σ_b p_b ((2/b - 2/n)(2 - 2/n) + v_n - v_b)`. -/
theorem lintegral_connectionTime_mul_panelTime {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    ∫⁻ p, ENNReal.ofReal (connectionTime s p * panelTime n p) ∂(trajectoryClockLaw n)
      = ENNReal.ofReal (∑ b ∈ Icc 1 n, stoppingProb s b *
          ((2 / (b : ℝ) - 2 / n) * (2 - 2 / (n : ℝ)) + (varTransitTime n - varTransitTime b))) :=
  lintegral_stoppingMix hn s
    (fun b ω ↦ (∑ j ∈ Ico (b - 1) (n - 1), ω j) * ∑ j ∈ Ico 0 (n - 1), ω j)
    (fun _ ↦ (measurable_sum_coords _).mul (measurable_sum_coords _))
    (fun b ↦ (2 / (b : ℝ) - 2 / n) * (2 - 2 / (n : ℝ)) + (varTransitTime n - varTransitTime b))
    (fun _ hb ↦ cross_value_nonneg (mem_Icc.mp hb).1 (mem_Icc.mp hb).2)
    (fun _ hb ↦ lintegral_connectionBlock_mul_panel (mem_Icc.mp hb).1 (mem_Icc.mp hb).2)

/-! ### The hidden load from the first moment -/

theorem sum_stoppingProb_mul_sub {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) (c : ℝ)
    (f : ℕ → ℝ) :
    ∑ b ∈ Icc 1 n, stoppingProb s b * (c - f b) = c - ∑ b ∈ Icc 1 n, stoppingProb s b * f b := by
  simp only [mul_sub, sum_sub_distrib]
  rw [← sum_mul, sum_stoppingProb hn s, one_mul]

theorem sum_stoppingProb_div_eq {n : ℕ} (s : Fin n → Fin n) :
    ∑ b ∈ Icc 1 n, stoppingProb s b / b = ∑ b ∈ Icc 1 n, stoppingProb s b * (1 / (b : ℝ)) :=
  sum_congr rfl fun _ _ ↦ div_eq_mul_one_div _ _

/-- The mean of the inverse hidden load is at least `1/n`. -/
theorem one_div_le_sum_stoppingProb_div {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    1 / (n : ℝ) ≤ ∑ b ∈ Icc 1 n, stoppingProb s b * (1 / (b : ℝ)) := by
  calc 1 / (n : ℝ) = ∑ b ∈ Icc 1 n, stoppingProb s b * (1 / (n : ℝ)) := by
        rw [← sum_mul, sum_stoppingProb hn s, one_mul]
    _ ≤ ∑ b ∈ Icc 1 n, stoppingProb s b * (1 / (b : ℝ)) := by
        refine sum_le_sum fun b hb ↦ mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (mem_Icc.mp hb).1
        have hbn : (b : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hb).2
        exact one_div_le_one_div_of_le (by linarith) hbn

/-- The (D8) value is nonnegative. -/
theorem connectionTime_mean_formula_nonneg {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    0 ≤ 2 * ∑ b ∈ Icc 1 n, stoppingProb s b / b - 2 / (n : ℝ) := by
  have h := one_div_le_sum_stoppingProb_div hn s
  rw [sum_stoppingProb_div_eq, show 2 / (n : ℝ) = 2 * (1 / n) by ring]
  linarith

/-- **The first moment of the connection clock identifies the harmonic mean of the hidden load at
connection**: `E[1/B] = E τ_q/2 + 1/n`. -/
theorem inv_stoppingLevel_mean_eq {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    (∫⁻ p, ENNReal.ofReal (1 / (stoppingLevel s p.1 : ℝ)) ∂(trajectoryClockLaw n)).toReal
      = (∫⁻ p, ENNReal.ofReal (connectionTime s p) ∂(trajectoryClockLaw n)).toReal / 2
        + 1 / (n : ℝ) := by
  have hm := one_div_le_sum_stoppingProb_div hn s
  rw [lintegral_inv_stoppingLevel hn s, connectionTime_mean hn s,
    ENNReal.toReal_ofReal ((by positivity : (0 : ℝ) ≤ 1 / n).trans hm),
    ENNReal.toReal_ofReal (connectionTime_mean_formula_nonneg hn s), sum_stoppingProb_div_eq]
  ring

theorem two_le_add_one_div {x : ℝ} (hx : 0 < x) : 2 ≤ x + 1 / x := by
  have hx0 : x ≠ 0 := hx.ne'
  have h : x + 1 / x - 2 = (x - 1) ^ 2 / x := by
    field_simp
    ring
  have hnn : 0 ≤ (x - 1) ^ 2 / x := div_nonneg (sq_nonneg _) hx.le
  linarith

/-- **The mean hidden load times the mean inverse hidden load is at least one.** -/
theorem one_le_mean_mul_mean_inv {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    1 ≤ (∑ b ∈ Icc 1 n, stoppingProb s b * (b : ℝ))
      * ∑ b ∈ Icc 1 n, stoppingProb s b * (1 / (b : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmpos : 0 < ∑ b ∈ Icc 1 n, stoppingProb s b * (1 / (b : ℝ)) :=
    lt_of_lt_of_le (one_div_pos.mpr hnR) (one_div_le_sum_stoppingProb_div hn s)
  generalize hM : ∑ b ∈ Icc 1 n, stoppingProb s b * (1 / (b : ℝ)) = M at hmpos ⊢
  have hterm : ∀ b ∈ Icc 1 n, stoppingProb s b * 2
      ≤ M * (stoppingProb s b * b) + 1 / M * (stoppingProb s b * (1 / (b : ℝ))) := by
    intro b hb
    have hbpos : (0 : ℝ) < b := by exact_mod_cast (mem_Icc.mp hb).1
    calc stoppingProb s b * 2 ≤ stoppingProb s b * ((b : ℝ) * M + 1 / ((b : ℝ) * M)) :=
          mul_le_mul_of_nonneg_left (two_le_add_one_div (mul_pos hbpos hmpos))
            ENNReal.toReal_nonneg
      _ = M * (stoppingProb s b * b) + 1 / M * (stoppingProb s b * (1 / (b : ℝ))) := by ring
  have hsum := sum_le_sum hterm
  rw [← sum_mul, sum_stoppingProb hn s, sum_add_distrib, ← mul_sum, ← mul_sum, hM,
    one_div_mul_cancel hmpos.ne'] at hsum
  linarith

/-- **The hidden load at connection, from the first moment**: `E B ≥ 2n/(n E τ_q + 2)`. -/
theorem two_mul_div_le_mean_stoppingLevel {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    2 * n / (n * (∫⁻ p, ENNReal.ofReal (connectionTime s p) ∂(trajectoryClockLaw n)).toReal + 2)
      ≤ (∫⁻ p, ENNReal.ofReal (stoppingLevel s p.1 : ℝ) ∂(trajectoryClockLaw n)).toReal := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmpos : 0 < ∑ b ∈ Icc 1 n, stoppingProb s b * (1 / (b : ℝ)) :=
    lt_of_lt_of_le (one_div_pos.mpr hnR) (one_div_le_sum_stoppingProb_div hn s)
  have hτ := inv_stoppingLevel_mean_eq hn s
  rw [lintegral_inv_stoppingLevel hn s, ENNReal.toReal_ofReal hmpos.le] at hτ
  have hden : (n : ℝ) * (∫⁻ p, ENNReal.ofReal (connectionTime s p) ∂(trajectoryClockLaw n)).toReal
      + 2 = 2 * n * ∑ b ∈ Icc 1 n, stoppingProb s b * (1 / (b : ℝ)) := by
    have hτ' : (∫⁻ p, ENNReal.ofReal (connectionTime s p) ∂(trajectoryClockLaw n)).toReal
        = 2 * (∑ b ∈ Icc 1 n, stoppingProb s b * (1 / (b : ℝ))) - 2 / n := by
      linarith
    rw [hτ', mul_sub, mul_div_assoc', mul_div_cancel_left₀ (2 : ℝ) hnR.ne']
    ring
  have hB : 0 ≤ ∑ b ∈ Icc 1 n, stoppingProb s b * (b : ℝ) :=
    sum_nonneg fun b _ ↦ mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg b)
  rw [lintegral_stoppingLevel hn s, ENNReal.toReal_ofReal hB, hden,
    div_le_iff₀ (mul_pos (mul_pos two_pos hnR) hmpos)]
  have h1 := mul_le_mul_of_nonneg_left (one_le_mean_mul_mean_inv hn s) hnR.le
  nlinarith

/-! ### The corrected clock and its error -/

/-- **The residual mean is the gap between the panel clock and the connection clock**:
`E R = 2 - 2/n - E τ_q`. -/
theorem residualTime_mean_eq {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    (∫⁻ p, ENNReal.ofReal (residualTime s p) ∂(trajectoryClockLaw n)).toReal
      = 2 - 2 / (n : ℝ)
        - (∫⁻ p, ENNReal.ofReal (connectionTime s p) ∂(trajectoryClockLaw n)).toReal := by
  have hR : 0 ≤ ∑ b ∈ Icc 1 n, stoppingProb s b * (2 - 2 / (b : ℝ)) :=
    sum_nonneg fun b hb ↦ mul_nonneg ENNReal.toReal_nonneg
      (two_sub_two_div_nonneg (mem_Icc.mp hb).1)
  rw [lintegral_residualTime hn s, connectionTime_mean hn s, ENNReal.toReal_ofReal hR,
    ENNReal.toReal_ofReal (connectionTime_mean_formula_nonneg hn s), sum_stoppingProb_mul_sub hn s,
    sum_stoppingProb_div_eq]
  have h2 : ∑ b ∈ Icc 1 n, stoppingProb s b * (2 / (b : ℝ))
      = 2 * ∑ b ∈ Icc 1 n, stoppingProb s b * (1 / (b : ℝ)) := by
    rw [mul_sum]
    exact sum_congr rfl fun b _ ↦ by ring
  rw [h2]
  ring

/-- **The panel clock is the connection clock plus the residual clock, in mean**, so
`τ_q + (2 - 2/n - E τ_q)` is an unbiased predictor of `T_n`. -/
theorem panelTime_mean_eq_add {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    (∫⁻ p, ENNReal.ofReal (panelTime n p) ∂(trajectoryClockLaw n)).toReal
      = (∫⁻ p, ENNReal.ofReal (connectionTime s p) ∂(trajectoryClockLaw n)).toReal
        + (∫⁻ p, ENNReal.ofReal (residualTime s p) ∂(trajectoryClockLaw n)).toReal := by
  rw [lintegral_panelTime hn s, residualTime_mean_eq hn s,
    ENNReal.toReal_ofReal (two_sub_two_div_nonneg (show 1 ≤ n by omega))]
  ring

theorem sum_stoppingProb_two_div_sub {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    ∑ b ∈ Icc 1 n, stoppingProb s b * (2 / (b : ℝ) - 2 / n)
      = 2 * ∑ b ∈ Icc 1 n, stoppingProb s b / b - 2 / (n : ℝ) := by
  simp only [mul_sub, sum_sub_distrib]
  rw [← sum_mul, sum_stoppingProb hn s, one_mul, mul_sum]
  congr 1
  exact sum_congr rfl fun b _ ↦ by ring

/-- **The covariance of the connection clock and the panel clock** is the variance of the holding
times the report sees: `Cov(τ_q, T_n) = Σ_b p_b (v_n - v_b)`. -/
theorem covariance_connectionTime_panelTime {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    (∫⁻ p, ENNReal.ofReal (connectionTime s p * panelTime n p) ∂(trajectoryClockLaw n)).toReal
      - (∫⁻ p, ENNReal.ofReal (connectionTime s p) ∂(trajectoryClockLaw n)).toReal
        * (∫⁻ p, ENNReal.ofReal (panelTime n p) ∂(trajectoryClockLaw n)).toReal
      = ∑ b ∈ Icc 1 n, stoppingProb s b * (varTransitTime n - varTransitTime b) := by
  have hcross : 0 ≤ ∑ b ∈ Icc 1 n, stoppingProb s b *
      ((2 / (b : ℝ) - 2 / n) * (2 - 2 / (n : ℝ)) + (varTransitTime n - varTransitTime b)) :=
    sum_nonneg fun b hb ↦ mul_nonneg ENNReal.toReal_nonneg
      (cross_value_nonneg (mem_Icc.mp hb).1 (mem_Icc.mp hb).2)
  rw [lintegral_connectionTime_mul_panelTime hn s, connectionTime_mean hn s,
    lintegral_panelTime hn s, ENNReal.toReal_ofReal hcross,
    ENNReal.toReal_ofReal (connectionTime_mean_formula_nonneg hn s),
    ENNReal.toReal_ofReal (two_sub_two_div_nonneg (show 1 ≤ n by omega))]
  simp only [mul_add, sum_add_distrib]
  have h1 : ∑ b ∈ Icc 1 n, stoppingProb s b * ((2 / (b : ℝ) - 2 / n) * (2 - 2 / (n : ℝ)))
      = (2 * ∑ b ∈ Icc 1 n, stoppingProb s b / b - 2 / (n : ℝ)) * (2 - 2 / (n : ℝ)) := by
    rw [← sum_stoppingProb_two_div_sub hn s, sum_mul]
    exact sum_congr rfl fun b _ ↦ by ring
  rw [h1]
  ring

/-- **The error of the corrected clock.** The mean square error of `τ_q + (2 - 2/n - E τ_q)` as a
predictor of `T_n` is `Var R = Σ_b p_b v_b + 4 Var(1/B)`. -/
theorem variance_residualTime_eq {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    (∫⁻ p, ENNReal.ofReal (residualTime s p ^ 2) ∂(trajectoryClockLaw n)).toReal
      - (∫⁻ p, ENNReal.ofReal (residualTime s p) ∂(trajectoryClockLaw n)).toReal ^ 2
      = ∑ b ∈ Icc 1 n, stoppingProb s b * varTransitTime b
        + 4 * (∑ b ∈ Icc 1 n, stoppingProb s b * (1 / (b : ℝ)) ^ 2
          - (∑ b ∈ Icc 1 n, stoppingProb s b * (1 / (b : ℝ))) ^ 2) := by
  have hR : 0 ≤ ∑ b ∈ Icc 1 n, stoppingProb s b * (2 - 2 / (b : ℝ)) :=
    sum_nonneg fun b hb ↦ mul_nonneg ENNReal.toReal_nonneg
      (two_sub_two_div_nonneg (mem_Icc.mp hb).1)
  have hR2 : 0 ≤ ∑ b ∈ Icc 1 n,
      stoppingProb s b * ((2 - 2 / (b : ℝ)) ^ 2 + varTransitTime b) :=
    sum_nonneg fun b _ ↦ mul_nonneg ENNReal.toReal_nonneg
      (add_nonneg (sq_nonneg _) (sum_nonneg fun k _ ↦ sq_nonneg _))
  rw [lintegral_sq_residualTime hn s, lintegral_residualTime hn s, ENNReal.toReal_ofReal hR2,
    ENNReal.toReal_ofReal hR]
  have e1 : ∑ b ∈ Icc 1 n, stoppingProb s b * ((2 - 2 / (b : ℝ)) ^ 2 + varTransitTime b)
      = 4 * ∑ b ∈ Icc 1 n, stoppingProb s b
        - 8 * ∑ b ∈ Icc 1 n, stoppingProb s b * (1 / (b : ℝ))
        + 4 * ∑ b ∈ Icc 1 n, stoppingProb s b * (1 / (b : ℝ)) ^ 2
        + ∑ b ∈ Icc 1 n, stoppingProb s b * varTransitTime b := by
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun b _ ↦ by ring
  have e2 : ∑ b ∈ Icc 1 n, stoppingProb s b * (2 - 2 / (b : ℝ))
      = 2 * ∑ b ∈ Icc 1 n, stoppingProb s b
        - 2 * ∑ b ∈ Icc 1 n, stoppingProb s b * (1 / (b : ℝ)) := by
    simp only [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun b _ ↦ by ring
  rw [e1, e2, sum_stoppingProb hn s]
  ring

/-- **The compressed Kingman clock overstates the connection clock**: `E τ_q ≤ 2 - 2/w`, Theorem C
on the path law. -/
theorem connectionTime_mean_le_two_sub {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n)
    (hw : 1 ≤ Linkage.width s) :
    (∫⁻ p, ENNReal.ofReal (connectionTime s p) ∂(trajectoryClockLaw n)).toReal
      ≤ 2 - 2 / (Linkage.width s : ℝ) := by
  rw [connectionTime_mean_eq_meanConnectionTime hn s, ENNReal.toReal_ofReal']
  exact max_le (meanConnectionTime_bot_le_two_sub s hw) (two_sub_two_div_nonneg hw)

/-- **The compressed Kingman clock understates the panel clock by `2/w - 2/n`.** -/
theorem panelTime_mean_sub_two_sub {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    (∫⁻ p, ENNReal.ofReal (panelTime n p) ∂(trajectoryClockLaw n)).toReal
      - (2 - 2 / (Linkage.width s : ℝ)) = 2 / (Linkage.width s : ℝ) - 2 / n := by
  rw [lintegral_panelTime hn s,
    ENNReal.toReal_ofReal (two_sub_two_div_nonneg (show 1 ≤ n by omega))]
  ring

/-! ### The observed intensity at the start -/

/-- **At the start the observed intensity is the product of the fiber sizes.** Under the point
prior at the fiber sizes `c`, the observed intensity of a visible merger of `C` and `D` is
`c_C c_D`.

Assumes: every fiber is nonempty, so the fiber sizes are a compatible load vector. -/
theorem observedIntensity_pointPrior {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℕ)
    (hc : ∀ C, 1 ≤ c C) (C D : ι) :
    observedIntensity c C D (fun L ↦ if L.1 = c then 1 else 0) = ((c C * c D : ℕ) : ℝ) := by
  have hmem : c ∈ loadStates c := mem_loadStates.mpr fun E ↦ ⟨hc E, le_rfl⟩
  rw [observedIntensity_eq_posteriorMean]
  have hone : ∑ L' : loadStates c, (if L'.1 = c then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single ⟨c, hmem⟩ (fun L _ hL ↦ if_neg fun h ↦ hL (Subtype.ext h))
      (fun h ↦ absurd (Finset.mem_univ _) h), if_pos rfl]
  rw [hone, Finset.sum_eq_single ⟨c, hmem⟩
    (fun L _ hL ↦ by rw [if_neg fun h ↦ hL (Subtype.ext h), zero_div, zero_mul])
    (fun h ↦ absurd (Finset.mem_univ _) h), if_pos rfl, div_one, one_mul]

/-- **The report's hazard at the start**: the visible intensity of the fiber sizes is
`C(n, 2) - Σ_i C(c_i, 2)`, where `n = Σ_i c_i`. -/
theorem loadVisibleIntensity_eq_choose_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℕ) :
    (loadVisibleIntensity c : ℝ) = ((∑ C, c C).choose 2 : ℝ) - ∑ C, ((c C).choose 2 : ℝ) := by
  have h := sum_choose_two_add_loadVisibleIntensity c
  have h' : ∑ C, ((c C).choose 2 : ℝ) + (loadVisibleIntensity c : ℝ)
      = ((∑ C, c C).choose 2 : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_add, h]
  linarith

/-- With two fibers the report's hazard at the start is `c₁ c₂`. -/
theorem loadVisibleIntensity_fin_two (c : Fin 2 → ℕ) : loadVisibleIntensity c = c 0 * c 1 := by
  have hpairs : (univ : Finset (Fin 2)).powersetCard 2 = {univ} := by
    simpa using Finset.powersetCard_self (univ : Finset (Fin 2))
  rw [loadVisibleIntensity, hpairs, sum_singleton, Fin.prod_univ_two]

end

end Descent.Pangenome.GraphCoalescent.HiddenClockCorrection
