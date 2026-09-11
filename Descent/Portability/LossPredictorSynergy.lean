/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.LossMomentRange

assert_below Descent.Decision Descent.Program

/-!
# Comparable marginal predictors and pure joint information

TQ Proposition 2.8. Part (a) builds two independent identically distributed
predictors whose conditional mean effects on the loss are the same nonconstant
function `f`, yet whose explainable fractions of individual squared loss are
equal and can be driven to zero by raising the kurtosis of the independent
multiplier alone; the exact fraction (2.20) is computed. Part (b) builds three
independent fair signs for which the realized loss is exactly `1 + cDZ`: neither
sign alone explains anything, while the pair explains everything. The kurtosis
witness reuses the tail family of `LossMomentRange`, and the loss algebra is
that of `mixture` and `total_variance` in `IndividualLossMoments`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.LossPredictorSynergy

open Foundations IndividualLossMoments

noncomputable section

variable {A N : Type*}

/-- TQ Proposition 2.8(a): the conditional second moment `m = M + f(D) + f(Z)`. -/
def comparableScale (M : ℝ) (f : A → ℝ) (d z : A) : ℝ := M + f d + f z

/-- The comparable-predictor residual `√m · U`, with `U` independent of both
predictors. -/
def comparableResidual (M : ℝ) (f : A → ℝ) (u : N → ℝ) (w : A × A × N) : ℝ :=
  Real.sqrt (comparableScale M f w.1 w.2.1) * u w.2.2

/-- The scale is positive once `M` exceeds twice a bound on `f`, which is the
manuscript's condition `M > 2‖f‖∞`. -/
theorem comparableScale_pos (M : ℝ) (f : A → ℝ) (bnd : ℝ) (hf : ∀ x, |f x| ≤ bnd)
    (hM : 2 * bnd < M) (d z : A) : 0 < comparableScale M f d z := by
  have h1 := abs_le.mp (hf d)
  have h2 := abs_le.mp (hf z)
  unfold comparableScale
  linarith [h1.1, h2.1]

/-- The realized loss is `m · U²`. -/
theorem comparableResidual_sq (M : ℝ) (f : A → ℝ) (u : N → ℝ) (bnd : ℝ)
    (hf : ∀ x, |f x| ≤ bnd) (hM : 2 * bnd < M) (d z : A) (n : N) :
    comparableResidual M f u (d, z, n) ^ 2
      = comparableScale M f d z * u n ^ 2 := by
  have hpos := comparableScale_pos M f bnd hf hM d z
  show (Real.sqrt (comparableScale M f d z) * u n) ^ 2 = _
  rw [mul_pow, Real.sq_sqrt hpos.le]

/-- The conditional mean loss given both predictors is exactly `m`. -/
theorem comparable_cell_mean (M : ℝ) (f : A → ℝ) (u : N → ℝ)
    (EU : ExpFunctional N) (bnd : ℝ) (hf : ∀ x, |f x| ≤ bnd) (hM : 2 * bnd < M)
    (hu2 : EU (fun n ↦ u n ^ 2) = 1) (d z : A) :
    EU (fun n ↦ comparableResidual M f u (d, z, n) ^ 2)
      = comparableScale M f d z := by
  have hfun : (fun n ↦ comparableResidual M f u (d, z, n) ^ 2)
      = comparableScale M f d z • (fun n ↦ u n ^ 2) := by
    funext n
    rw [comparableResidual_sq M f u bnd hf hM d z n]
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [hfun, EU.smul_eval, hu2]
  ring

/-- The conditional loss variance given both predictors is `(κ - 1)m²`. -/
theorem comparable_cell_variance (M : ℝ) (f : A → ℝ) (u : N → ℝ)
    (EU : ExpFunctional N) (bnd κ : ℝ) (hf : ∀ x, |f x| ≤ bnd) (hM : 2 * bnd < M)
    (hu2 : EU (fun n ↦ u n ^ 2) = 1) (hu4 : EU (fun n ↦ u n ^ 4) = κ) (d z : A) :
    variance EU (fun n ↦ comparableResidual M f u (d, z, n) ^ 2)
      = (κ - 1) * comparableScale M f d z ^ 2 := by
  have hfun : (fun n ↦ (comparableResidual M f u (d, z, n) ^ 2) ^ 2)
      = comparableScale M f d z ^ 2 • (fun n ↦ u n ^ 4) := by
    funext n
    rw [comparableResidual_sq M f u bnd hf hM d z n]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  simp only [variance_eq_expect_sq_sub_sq_mean]
  rw [hfun, EU.smul_eval, hu4, comparable_cell_mean M f u EU bnd hf hM hu2 d z]
  ring

/-- The conditional mean loss given one predictor alone is `M + f(D)`: both
predictors have exactly the same conditional mean effect. -/
theorem comparable_marginal_mean (M : ℝ) (f : A → ℝ) (u : N → ℝ)
    (E0 : ExpFunctional A) (EU : ExpFunctional N) (bnd : ℝ)
    (hf : ∀ x, |f x| ≤ bnd) (hM : 2 * bnd < M)
    (hu2 : EU (fun n ↦ u n ^ 2) = 1) (hf0 : E0 f = 0) (d : A) :
    mixture E0 (fun _ ↦ EU)
      (fun w ↦ comparableResidual M f u (d, w.1, w.2) ^ 2) = M + f d := by
  show E0 (fun z ↦ EU (fun n ↦ comparableResidual M f u (d, z, n) ^ 2)) = _
  simp only [comparable_cell_mean M f u EU bnd hf hM hu2]
  have hfun : (fun z ↦ comparableScale M f d z) = fun z ↦ M + f d + 1 * f z := by
    funext z
    unfold comparableScale
    ring
  rw [hfun, eval_affine, hf0]
  ring

/-- The conditional loss variance given one predictor alone. -/
theorem comparable_marginal_variance (M : ℝ) (f : A → ℝ) (u : N → ℝ)
    (E0 : ExpFunctional A) (EU : ExpFunctional N) (bnd κ : ℝ)
    (hf : ∀ x, |f x| ≤ bnd) (hM : 2 * bnd < M)
    (hu2 : EU (fun n ↦ u n ^ 2) = 1) (hu4 : EU (fun n ↦ u n ^ 4) = κ) (d : A) :
    variance (mixture E0 (fun _ ↦ EU))
        (fun w ↦ comparableResidual M f u (d, w.1, w.2) ^ 2)
      = (κ - 1) * E0 (fun z ↦ comparableScale M f d z ^ 2) + variance E0 f := by
  rw [total_variance E0 (fun _ ↦ EU)
    (fun w : A × N ↦ comparableResidual M f u (d, w.1, w.2) ^ 2)]
  show E0 (fun z ↦ variance EU (fun n ↦ comparableResidual M f u (d, z, n) ^ 2))
      + variance E0 (fun z ↦ EU (fun n ↦ comparableResidual M f u (d, z, n) ^ 2))
      = (κ - 1) * E0 (fun z ↦ comparableScale M f d z ^ 2) + variance E0 f
  simp only [comparable_cell_variance M f u EU bnd κ hf hM hu2 hu4,
    comparable_cell_mean M f u EU bnd hf hM hu2]
  have h1 : (fun z ↦ (κ - 1) * comparableScale M f d z ^ 2)
      = (κ - 1) • (fun z ↦ comparableScale M f d z ^ 2) := rfl
  have h2 : (fun z ↦ comparableScale M f d z) = fun z ↦ M + f d + 1 * f z := by
    funext z
    unfold comparableScale
    ring
  rw [h1, E0.smul_eval, h2, variance_affine]
  ring

/-- The exact total loss variance of the comparable-predictor construction. -/
theorem comparable_total_variance (M : ℝ) (f : A → ℝ) (u : N → ℝ)
    (E0 : ExpFunctional A) (EU : ExpFunctional N) (bnd κ : ℝ)
    (hf : ∀ x, |f x| ≤ bnd) (hM : 2 * bnd < M)
    (hu2 : EU (fun n ↦ u n ^ 2) = 1) (hu4 : EU (fun n ↦ u n ^ 4) = κ)
    (hf0 : E0 f = 0) :
    variance (mixture E0 (fun _ ↦ mixture E0 (fun _ ↦ EU)))
        (fun w ↦ comparableResidual M f u w ^ 2)
      = (κ - 1) * E0 (fun d ↦ E0 (fun z ↦ comparableScale M f d z ^ 2))
        + 2 * variance E0 f := by
  rw [total_variance E0 (fun _ ↦ mixture E0 (fun _ ↦ EU))
    (fun w : A × A × N ↦ comparableResidual M f u w ^ 2)]
  show E0 (fun d ↦ variance (mixture E0 (fun _ ↦ EU))
        (fun w : A × N ↦ comparableResidual M f u (d, w.1, w.2) ^ 2))
      + variance E0 (fun d ↦ mixture E0 (fun _ ↦ EU)
        (fun w : A × N ↦ comparableResidual M f u (d, w.1, w.2) ^ 2))
      = (κ - 1) * E0 (fun d ↦ E0 (fun z ↦ comparableScale M f d z ^ 2))
        + 2 * variance E0 f
  simp only [comparable_marginal_variance M f u E0 EU bnd κ hf hM hu2 hu4,
    comparable_marginal_mean M f u E0 EU bnd hf hM hu2 hf0]
  have h1 : (fun d ↦ (κ - 1) * E0 (fun z ↦ comparableScale M f d z ^ 2)
        + variance E0 f)
      = (κ - 1) • (fun d ↦ E0 (fun z ↦ comparableScale M f d z ^ 2))
        + (fun _ : A ↦ variance E0 f) := rfl
  have h2 : (fun d ↦ M + f d) = fun d ↦ M + 1 * f d := by
    funext d
    ring
  rw [h1, E0.add_eval, E0.smul_eval, E0.eval_const, h2, variance_affine]
  ring

/-- TQ (2.20): the exact marginal explainable fraction of individual squared
loss, the same for both predictors. -/
theorem comparable_explainable_fraction (M : ℝ) (f : A → ℝ) (u : N → ℝ)
    (E0 : ExpFunctional A) (EU : ExpFunctional N) (bnd κ : ℝ)
    (hf : ∀ x, |f x| ≤ bnd) (hM : 2 * bnd < M)
    (hu2 : EU (fun n ↦ u n ^ 2) = 1) (hu4 : EU (fun n ↦ u n ^ 4) = κ)
    (hf0 : E0 f = 0) :
    variance E0 (fun d ↦ mixture E0 (fun _ ↦ EU)
          (fun w ↦ comparableResidual M f u (d, w.1, w.2) ^ 2))
        / variance (mixture E0 (fun _ ↦ mixture E0 (fun _ ↦ EU)))
          (fun w ↦ comparableResidual M f u w ^ 2)
      = variance E0 f / (2 * variance E0 f
        + (κ - 1) * E0 (fun d ↦ E0 (fun z ↦ comparableScale M f d z ^ 2))) := by
  have hnum : variance E0 (fun d ↦ mixture E0 (fun _ ↦ EU)
      (fun w ↦ comparableResidual M f u (d, w.1, w.2) ^ 2)) = variance E0 f := by
    simp only [comparable_marginal_mean M f u E0 EU bnd hf hM hu2 hf0]
    have h2 : (fun d ↦ M + f d) = fun d ↦ M + 1 * f d := by
      funext d
      ring
    rw [h2, variance_affine]
    ring
  rw [hnum, comparable_total_variance M f u E0 EU bnd κ hf hM hu2 hu4 hf0]
  ring

/-- Exchanging which predictor is the outer summary leaves the residual
unchanged, so the two marginal fractions of TQ (2.20) are literally equal. -/
theorem comparableResidual_symm (M : ℝ) (f : A → ℝ) (u : N → ℝ)
    (d z : A) (n : N) :
    comparableResidual M f u (d, z, n) = comparableResidual M f u (z, d, n) := by
  unfold comparableResidual comparableScale
  rw [show M + f z + f d = M + f d + f z by ring]

/-- The equal fractions can be made arbitrarily small by raising the kurtosis
alone, with the conditional mean effect `f` untouched. -/
theorem comparable_fraction_arbitrarily_small (V W ε : ℝ) (hV : 0 < V)
    (hW : 0 < W) (hε : 0 < ε) :
    ∃ κ : ℝ, 1 ≤ κ ∧ V / (2 * V + (κ - 1) * W) < ε := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hWne : W ≠ 0 := ne_of_gt hW
  refine ⟨1 + V / (ε * W), by linarith [div_pos hV (mul_pos hε hW)], ?_⟩
  have hkey : (1 + V / (ε * W) - 1) * W = V / ε := by
    field_simp
  rw [hkey]
  have hdiv : 0 < V / ε := div_pos hV hε
  have hden : 0 < 2 * V + V / ε := by linarith
  rw [div_lt_iff₀ hden]
  have h1 : ε * (V / ε) = V := by field_simp
  nlinarith [h1, mul_pos hε hV]

/-- Every kurtosis `κ ≥ 1` is realized by an explicit three-point law: the tail
family of `LossMomentRange` at its unit-variance cell. -/
theorem kurtosis_witness (κ : ℝ) (hκ : 1 ≤ κ) :
    LossMomentRange.tailLaw κ hκ
        (fun i ↦ LossMomentRange.residual κ (false, i)) = 0 ∧
      LossMomentRange.tailLaw κ hκ
        (fun i ↦ LossMomentRange.residual κ (false, i) ^ 2) = 1 ∧
      LossMomentRange.tailLaw κ hκ
        (fun i ↦ LossMomentRange.residual κ (false, i) ^ 4) = κ := by
  obtain ⟨h1, h2, h3⟩ := LossMomentRange.conditional_moments κ hκ false
  refine ⟨h1, ?_, ?_⟩
  · rw [h2]
    norm_num [LossMomentRange.conditionalVariance]
  · rw [h3]
    norm_num [LossMomentRange.conditionalVariance]

/-- TQ Proposition 2.8(b): the pure-joint-information residual `√(1 + cDZ)·U` on
three independent fair signs. -/
def synergyResidual (c : ℝ) (w : Bool × Bool × Bool) : ℝ :=
  Real.sqrt (1 + c * (if w.1 then 1 else -1) * (if w.2.1 then 1 else -1))
    * (if w.2.2 then 1 else -1)

/-- Its realized loss `1 + cDZ`, which the pair determines exactly. -/
def synergyLoss (c : ℝ) (w : Bool × Bool × Bool) : ℝ :=
  1 + c * (if w.1 then 1 else -1) * (if w.2.1 then 1 else -1)

/-- The residual's square is the joint-information loss: the multiplier's square
is one, so the loss carries no information beyond the pair. -/
theorem synergyResidual_sq (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    (fun w ↦ synergyResidual c w ^ 2) = synergyLoss c := by
  funext w
  obtain ⟨d, z, n⟩ := w
  have hX : (0 : ℝ)
      ≤ 1 + c * (if d then (1 : ℝ) else -1) * (if z then (1 : ℝ) else -1) := by
    cases d <;> cases z <;> norm_num <;> linarith
  have hs : ((if n then (1 : ℝ) else -1)) ^ 2 = 1 := by
    cases n <;> norm_num
  show (Real.sqrt (1 + c * (if d then (1 : ℝ) else -1) * (if z then (1 : ℝ) else -1))
      * (if n then (1 : ℝ) else -1)) ^ 2
      = 1 + c * (if d then (1 : ℝ) else -1) * (if z then (1 : ℝ) else -1)
  rw [mul_pow, Real.sq_sqrt hX, hs, mul_one]

/-- Evaluation against two independent fair signs. -/
theorem doubleUniform_apply (g : Bool × Bool → ℝ) :
    mixture (uniformExp Bool) (fun _ ↦ uniformExp Bool) g
      = (g (false, false) + g (false, true) + g (true, false) + g (true, true))
        / 4 := by
  show uniformExp Bool (fun d ↦ uniformExp Bool (fun z ↦ g (d, z))) = _
  simp only [uniformExp_apply, Fintype.sum_bool, Fintype.card_bool, Nat.cast_ofNat]
  ring

/-- Evaluation against three independent fair signs, the sign grouped last. -/
theorem tripleUniform_apply (g : Bool × Bool × Bool → ℝ) :
    mixture (uniformExp Bool)
        (fun _ ↦ mixture (uniformExp Bool) (fun _ ↦ uniformExp Bool)) g
      = (g (false, false, false) + g (false, false, true) + g (false, true, false)
        + g (false, true, true) + g (true, false, false) + g (true, false, true)
        + g (true, true, false) + g (true, true, true)) / 8 := by
  show uniformExp Bool (fun d ↦ uniformExp Bool (fun z ↦
    uniformExp Bool (fun n ↦ g (d, z, n)))) = _
  simp only [uniformExp_apply, Fintype.sum_bool, Fintype.card_bool, Nat.cast_ofNat]
  ring

/-- Evaluation against three independent fair signs, the pair grouped first. -/
theorem pairUniform_apply (g : (Bool × Bool) × Bool → ℝ) :
    mixture (mixture (uniformExp Bool) (fun _ ↦ uniformExp Bool))
        (fun _ ↦ uniformExp Bool) g
      = (g ((false, false), false) + g ((false, false), true)
        + g ((false, true), false) + g ((false, true), true)
        + g ((true, false), false) + g ((true, false), true)
        + g ((true, true), false) + g ((true, true), true)) / 8 := by
  show uniformExp Bool (fun d ↦ uniformExp Bool (fun z ↦
    uniformExp Bool (fun n ↦ g ((d, z), n)))) = _
  simp only [uniformExp_apply, Fintype.sum_bool, Fintype.card_bool, Nat.cast_ofNat]
  ring

/-- The total loss variance of the synergy construction is exactly `c²`. -/
theorem synergy_total_variance (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    variance (mixture (uniformExp Bool)
        (fun _ ↦ mixture (uniformExp Bool) (fun _ ↦ uniformExp Bool)))
      (fun w ↦ synergyResidual c w ^ 2) = c ^ 2 := by
  rw [synergyResidual_sq c hc hc1]
  simp only [variance_eq_expect_sq_sub_sq_mean]
  rw [tripleUniform_apply (fun w ↦ synergyLoss c w ^ 2),
    tripleUniform_apply (synergyLoss c)]
  norm_num [synergyLoss]
  all_goals ring

/-- TQ (2.21): the conditional mean loss given either sign alone is constant, so
the marginal explainable fraction of that sign is exactly zero. -/
theorem synergy_marginal_numerator (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    variance (uniformExp Bool) (fun d ↦ mixture (uniformExp Bool)
      (fun _ ↦ uniformExp Bool)
      (fun w ↦ synergyResidual c (d, w.1, w.2) ^ 2)) = 0 := by
  have hinner : (fun d ↦ mixture (uniformExp Bool) (fun _ ↦ uniformExp Bool)
      (fun w ↦ synergyResidual c (d, w.1, w.2) ^ 2)) = fun _ : Bool ↦ (1 : ℝ) := by
    funext d
    have hfun : (fun w : Bool × Bool ↦ synergyResidual c (d, w.1, w.2) ^ 2)
        = fun w : Bool × Bool ↦ synergyLoss c (d, w.1, w.2) := by
      funext w
      exact congrFun (synergyResidual_sq c hc hc1) (d, w.1, w.2)
    rw [hfun, doubleUniform_apply]
    cases d <;> norm_num [synergyLoss]
  rw [hinner]
  norm_num [variance_eq_expect_sq_sub_sq_mean]

/-- TQ (2.21): each single sign explains none of the individual loss variation. -/
theorem synergy_marginal_fraction (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    variance (uniformExp Bool) (fun d ↦ mixture (uniformExp Bool)
          (fun _ ↦ uniformExp Bool)
          (fun w ↦ synergyResidual c (d, w.1, w.2) ^ 2))
        / variance (mixture (uniformExp Bool)
          (fun _ ↦ mixture (uniformExp Bool) (fun _ ↦ uniformExp Bool)))
          (fun w ↦ synergyResidual c w ^ 2) = 0 := by
  rw [synergy_marginal_numerator c hc hc1, zero_div]

/-- The same residual, presented with the pair of signs as the summary. -/
def synergyPairResidual (c : ℝ) (w : (Bool × Bool) × Bool) : ℝ :=
  synergyResidual c (w.1.1, w.1.2, w.2)

/-- The between-pair variance of the conditional mean loss is exactly `c²`. -/
theorem synergy_pair_numerator (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    variance (mixture (uniformExp Bool) (fun _ ↦ uniformExp Bool))
      (fun p ↦ uniformExp Bool (fun n ↦ synergyPairResidual c (p, n) ^ 2))
      = c ^ 2 := by
  have hinner : (fun p : Bool × Bool ↦
      uniformExp Bool (fun n ↦ synergyPairResidual c (p, n) ^ 2))
      = fun p : Bool × Bool ↦
        1 + c * (if p.1 then (1 : ℝ) else -1) * (if p.2 then (1 : ℝ) else -1) := by
    funext p
    have hfun : (fun n ↦ synergyPairResidual c (p, n) ^ 2)
        = fun n ↦ synergyLoss c (p.1, p.2, n) := by
      funext n
      exact congrFun (synergyResidual_sq c hc hc1) (p.1, p.2, n)
    rw [hfun]
    simp only [uniformExp_apply, Fintype.sum_bool, Fintype.card_bool,
      Nat.cast_ofNat, synergyLoss]
    ring
  rw [hinner]
  simp only [variance_eq_expect_sq_sub_sq_mean]
  rw [doubleUniform_apply, doubleUniform_apply]
  norm_num
  all_goals ring

/-- The total loss variance in the pair grouping is the same `c²`. -/
theorem synergy_pair_total_variance (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    variance (mixture (mixture (uniformExp Bool) (fun _ ↦ uniformExp Bool))
        (fun _ ↦ uniformExp Bool)) (fun w ↦ synergyPairResidual c w ^ 2)
      = c ^ 2 := by
  have hfun : (fun w : (Bool × Bool) × Bool ↦ synergyPairResidual c w ^ 2)
      = fun w : (Bool × Bool) × Bool ↦ synergyLoss c (w.1.1, w.1.2, w.2) := by
    funext w
    exact congrFun (synergyResidual_sq c hc hc1) (w.1.1, w.1.2, w.2)
  rw [hfun]
  simp only [variance_eq_expect_sq_sub_sq_mean]
  rw [pairUniform_apply (fun w ↦ synergyLoss c (w.1.1, w.1.2, w.2) ^ 2),
    pairUniform_apply (fun w ↦ synergyLoss c (w.1.1, w.1.2, w.2))]
  norm_num [synergyLoss]
  all_goals ring

/-- TQ (2.21): the pair of signs explains all of the individual loss variation,
though neither sign alone explains any of it. -/
theorem synergy_pair_fraction (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    variance (mixture (uniformExp Bool) (fun _ ↦ uniformExp Bool))
          (fun p ↦ uniformExp Bool (fun n ↦ synergyPairResidual c (p, n) ^ 2))
        / variance (mixture (mixture (uniformExp Bool) (fun _ ↦ uniformExp Bool))
          (fun _ ↦ uniformExp Bool)) (fun w ↦ synergyPairResidual c w ^ 2)
      = 1 := by
  rw [synergy_pair_numerator c hc hc1, synergy_pair_total_variance c hc hc1,
    div_self (ne_of_gt (pow_pos hc 2))]

end

end Descent.Portability.LossPredictorSynergy
