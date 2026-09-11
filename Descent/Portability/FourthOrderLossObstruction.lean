/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IndividualLossMoments
import Descent.Portability.TraitPortabilityRange

assert_below Descent.Decision Descent.Program

/-!
# A fourth-order obstruction to individual-loss identification

TQ Theorem 8.2. Two hierarchical context mixtures `E` and `O` are built on the same
four-sign latent effect state, the same genotype law, and the same source law. They
agree on every joint law of at most three effect signs, on every conditional first and
second moment of score and outcome, on cellwise mean squared error, on the pooled
within-cell squared correlation, and on the expected squared correlation given the
sampled effect state. They nevertheless report distance-explainable loss fractions
`1/12` and `2/27`. The only hypotheses are the domain conditions of the construction
(a mixing weight in `[0,1]`); nothing assumes the conclusion.

The laws are finitely supported and built with `Portability.weightedExp` and
`Portability.uniformExp`; the hierarchy is `IndividualLossMoments.mixture`, and the
between/within split is `IndividualLossMoments.total_variance`. The reported fraction is
`Foundations.explainableFraction` of `Foundations.variance`, and the effect sign is the
corpus' `TraitPortabilityRange.sign`.

## Empirical status

None. The bodies here are algebra: a four-sign parity law, a squared-loss expansion and a
between-over-total ratio are claims about a model, and what carries an empirical status is
a named quantity in a subsystem module asserting that this algebra computes something
measurable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FourthOrderLossObstruction

open Foundations IndividualLossMoments

noncomputable section

/-- One draw of the four latent effect signs, encoded as Booleans. -/
abbrev EffectContext : Type := Bool × Bool × Bool × Bool

/-- The `±1` effect sign carried by one Boolean coordinate: the corpus'
`TraitPortabilityRange.sign`. -/
def effectSign : Bool → ℝ := TraitPortabilityRange.sign

/-- The effect sign is the corpus' `TraitPortabilityRange.sign`. -/
theorem effectSign_eq_sign : effectSign = TraitPortabilityRange.sign := rfl

/-- The effect sign takes the values `1` and `-1`. -/
theorem effectSign_apply (b : Bool) : effectSign b = if b then 1 else -1 := rfl

/-- `true` exactly when the product of the four effect signs is `+1`. -/
def evenParity (z : EffectContext) : Bool :=
  !(xor (xor z.1 z.2.1) (xor z.2.2.1 z.2.2.2))

/-- The average effect sign `c(Z)` of a latent context. -/
def effectMean (z : EffectContext) : ℝ :=
  (effectSign z.1 + effectSign z.2.1 + effectSign z.2.2.1 + effectSign z.2.2.2) / 4

/-- The uniform law on the parity class selected by `par`: model `E` uses `par = true`
(product of signs `+1`), model `O` uses `par = false`. -/
def parityWeight (par : Bool) (z : EffectContext) : ℝ :=
  if evenParity z = par then 1 / 8 else 0

/-- The conditional latent-context law inside a distance cell: mass `1 - θ` on the
all-positive state and mass `θ` spread uniformly over one parity class. -/
def contextWeight (par : Bool) (θ : ℝ) (z : EffectContext) : ℝ :=
  (1 - θ) * (if z = (true, true, true, true) then 1 else 0) + θ * parityWeight par z

/-- Both parity classes carry total mass one. -/
theorem parityWeight_sum (par : Bool) : ∑ z, parityWeight par z = 1 := by
  cases par <;>
    simp [parityWeight, evenParity, Fintype.sum_prod_type] <;> norm_num

/-- Each latent context weight is nonnegative when the mixing weight is a probability. -/
theorem contextWeight_nonneg (par : Bool) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (z : EffectContext) : 0 ≤ contextWeight par θ z := by
  have hpar : (0 : ℝ) ≤ parityWeight par z := by
    unfold parityWeight; split <;> norm_num
  have hind : (0 : ℝ) ≤ (if z = (true, true, true, true) then 1 else 0) := by
    split <;> norm_num
  have hθ : (0 : ℝ) ≤ 1 - θ := by linarith
  exact add_nonneg (mul_nonneg hθ hind) (mul_nonneg h0 hpar)

/-- The latent context weights sum to one. -/
theorem contextWeight_sum (par : Bool) (θ : ℝ) : ∑ z, contextWeight par θ z = 1 := by
  cases par <;>
    simp [contextWeight, parityWeight, evenParity, Fintype.sum_prod_type] <;> ring

/-- The conditional latent-context expectation inside one distance cell. -/
def contextExp (par : Bool) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ExpFunctional EffectContext :=
  weightedExp (contextWeight par θ) (contextWeight_nonneg par θ h0 h1)
    (contextWeight_sum par θ)

/-- The two distance cells carry mixing weights `1/4` and `3/4`. -/
def cellTheta : Fin 2 → ℝ := fun d ↦ if d = 0 then 1 / 4 else 3 / 4

/-- The mixing weight of each cell lies in `[0,1]`. -/
theorem cellTheta_mem (d : Fin 2) : 0 ≤ cellTheta d ∧ cellTheta d ≤ 1 := by
  unfold cellTheta; split <;> norm_num

/-- The latent-context law in distance cell `d`. -/
def cellExp (par : Bool) (d : Fin 2) : ExpFunctional EffectContext :=
  contextExp par (cellTheta d) (cellTheta_mem d).1 (cellTheta_mem d).2

/-- Latent context and individual genotype/noise draw inside one distance cell. -/
def innerExp (par : Bool) (d : Fin 2) : ExpFunctional (EffectContext × (Bool × Bool)) :=
  mixture (cellExp par d) (fun _ ↦ uniformExp (Bool × Bool))

/-- The full hierarchical law: distance cell, then latent context, then individual draw. -/
def jointExp (par : Bool) : ExpFunctional (Fin 2 × (EffectContext × (Bool × Bool))) :=
  mixture (uniformExp (Fin 2)) (innerExp par)

/-- The cell law is the corpus' `IndividualLossMoments.mixture` of the latent-context
law with the uniform genotype/noise draw. -/
theorem innerExp_eq_mixture (par : Bool) (d : Fin 2) :
    innerExp par d = mixture (cellExp par d) (fun _ ↦ uniformExp (Bool × Bool)) := rfl

/-- The hierarchical law is the corpus' `IndividualLossMoments.mixture` of the uniform
distance-cell law with the within-cell law. -/
theorem jointExp_eq_mixture (par : Bool) :
    jointExp par = mixture (uniformExp (Fin 2)) (innerExp par) := rfl

/-- The source-frozen score: four perfectly linked copies of one fair genotype sign. -/
def score (ω : Fin 2 × (EffectContext × (Bool × Bool))) : ℝ := effectSign ω.2.2.1

/-- The deployed outcome `Y = c(Z)X + sqrt(1 - c(Z)^2) U`. -/
def outcome (ω : Fin 2 × (EffectContext × (Bool × Bool))) : ℝ :=
  effectMean ω.2.1 * effectSign ω.2.2.1 +
    Real.sqrt (1 - effectMean ω.2.1 ^ 2) * effectSign ω.2.2.2

/-- The individual squared prediction error. -/
def individualLoss (ω : Fin 2 × (EffectContext × (Bool × Bool))) : ℝ :=
  (outcome ω - score ω) ^ 2

/-- The average effect sign never leaves `[-1,1]`, so the outcome is real. -/
theorem effectMean_sq_le_one (z : EffectContext) : effectMean z ^ 2 ≤ 1 := by
  obtain ⟨a, b, c, e⟩ := z
  cases a <;> cases b <;> cases c <;> cases e <;> norm_num [effectMean, effectSign]

/-- The residual scale squares back to `1 - c(Z)^2`. -/
theorem sqrt_residual_sq (z : EffectContext) :
    Real.sqrt (1 - effectMean z ^ 2) ^ 2 = 1 - effectMean z ^ 2 :=
  Real.sq_sqrt (by have := effectMean_sq_le_one z; linarith)

/-- Conditional mean individual loss given the latent effect state: `2(1 - c)`. -/
theorem noise_loss_mean (d : Fin 2) (z : EffectContext) :
    uniformExp (Bool × Bool) (fun p ↦ individualLoss (d, (z, p))) =
      2 * (1 - effectMean z) := by
  have hb := sqrt_residual_sq z
  simp only [uniformExp_apply, Fintype.sum_prod_type, Fintype.sum_bool, individualLoss,
    outcome, score, effectSign_apply, Fintype.card_prod, Fintype.card_bool]
  norm_num
  linear_combination hb

/-- Conditional second moment of individual loss given the latent effect state. -/
def lossSecondMoment (z : EffectContext) : ℝ :=
  4 * (1 - effectMean z) ^ 2 + 4 * (1 - effectMean z) ^ 2 * (1 - effectMean z ^ 2)

/-- The conditional second moment of individual loss is the squared conditional mean
plus `4(c-1)^2(1-c^2)`, with no surviving odd noise term. -/
theorem noise_loss_second_moment (d : Fin 2) (z : EffectContext) :
    uniformExp (Bool × Bool) (fun p ↦ individualLoss (d, (z, p)) ^ 2) =
      lossSecondMoment z := by
  have hb := sqrt_residual_sq z
  simp only [uniformExp_apply, Fintype.sum_prod_type, Fintype.sum_bool, individualLoss,
    outcome, score, effectSign_apply, lossSecondMoment, Fintype.card_prod, Fintype.card_bool]
  norm_num
  linear_combination
    (6 * (effectMean z - 1) ^ 2 + (1 - effectMean z ^ 2) +
      Real.sqrt (1 - effectMean z ^ 2) ^ 2) * hb

/-- **The law of the mean effect sign.** Under `P₊` it is `1, 0, -1` with probabilities
`1/8, 6/8, 1/8`; under `P₋` it is `±1/2` with probability `1/2` each. Every parity
average below is an instance of this one identity. -/
theorem parity_expectation (par : Bool) (g : ℝ → ℝ) :
    ∑ z, parityWeight par z * g (effectMean z) =
      if par then (g 1 + 6 * g 0 + g (-1)) / 8 else (g (1 / 2) + g (-1 / 2)) / 2 := by
  cases par <;>
    simp [parityWeight, evenParity, effectMean, effectSign_apply,
      Fintype.sum_prod_type] <;> ring

/-- Mean effect sign under either parity class is zero. -/
theorem parity_effectMean (par : Bool) :
    ∑ z, parityWeight par z * effectMean z = 0 := by
  cases par
  · have h := parity_expectation false (fun x : ℝ ↦ x)
    norm_num at h
    exact h
  · have h := parity_expectation true (fun x : ℝ ↦ x)
    norm_num at h
    exact h

/-- Second moment of the mean effect sign is `1/4` under either parity class: the two
models share every second-order effect summary. -/
theorem parity_effectMean_sq (par : Bool) :
    ∑ z, parityWeight par z * effectMean z ^ 2 = 1 / 4 := by
  cases par
  · have h := parity_expectation false (fun x : ℝ ↦ x ^ 2)
    norm_num at h
    exact h
  · have h := parity_expectation true (fun x : ℝ ↦ x ^ 2)
    norm_num at h
    exact h

/-- Fourth moments of the mean effect sign separate the two parity classes: `1/4`
against `1/16`. This is the fourth-order coordinate the report depends on. -/
theorem parity_effectMean_fourth (par : Bool) :
    ∑ z, parityWeight par z * effectMean z ^ 4 = if par then 1 / 4 else 1 / 16 := by
  cases par
  · have h := parity_expectation false (fun x : ℝ ↦ x ^ 4)
    norm_num at h
    exact h
  · have h := parity_expectation true (fun x : ℝ ↦ x ^ 4)
    norm_num at h
    exact h

/-- Conditional second moment of loss under a parity class: `8` against `35/4`. -/
theorem parity_lossSecondMoment (par : Bool) :
    ∑ z, parityWeight par z * lossSecondMoment z = if par then 8 else 35 / 4 := by
  simp only [lossSecondMoment]
  cases par
  · have h := parity_expectation false
      (fun x : ℝ ↦ 4 * (1 - x) ^ 2 + 4 * (1 - x) ^ 2 * (1 - x ^ 2))
    norm_num at h
    exact h
  · have h := parity_expectation true
      (fun x : ℝ ↦ 4 * (1 - x) ^ 2 + 4 * (1 - x) ^ 2 * (1 - x ^ 2))
    norm_num at h
    exact h

/-- **Every joint law of at most three effect signs agrees between the two models.**
Each of the four three-coordinate marginals is uniform under both parity classes, so
any function of at most three signs has the same expectation under both. -/
theorem three_sign_marginals_agree (g : Bool → Bool → Bool → ℝ) :
    (∑ z, parityWeight true z * g z.1 z.2.1 z.2.2.1 =
        ∑ z, parityWeight false z * g z.1 z.2.1 z.2.2.1) ∧
      (∑ z, parityWeight true z * g z.1 z.2.1 z.2.2.2 =
        ∑ z, parityWeight false z * g z.1 z.2.1 z.2.2.2) ∧
      (∑ z, parityWeight true z * g z.1 z.2.2.1 z.2.2.2 =
        ∑ z, parityWeight false z * g z.1 z.2.2.1 z.2.2.2) ∧
      (∑ z, parityWeight true z * g z.2.1 z.2.2.1 z.2.2.2 =
        ∑ z, parityWeight false z * g z.2.1 z.2.2.1 z.2.2.2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [parityWeight, evenParity, Fintype.sum_prod_type] <;> ring

/-- Expectation against the cell context law of a function vanishing at the
all-positive state reduces to `θ` times its parity-class average. -/
theorem cellExp_apply (par : Bool) (d : Fin 2) (f : EffectContext → ℝ) :
    cellExp par d f =
      (1 - cellTheta d) * f (true, true, true, true) +
        cellTheta d * ∑ z, parityWeight par z * f z := by
  show ∑ z, contextWeight par (cellTheta d) z * f z = _
  have hsplit : ∀ z : EffectContext, contextWeight par (cellTheta d) z * f z =
      (1 - cellTheta d) *
          (if z = ((true, true, true, true) : EffectContext) then f z else 0) +
        cellTheta d * (parityWeight par z * f z) := by
    intro z
    unfold contextWeight
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun z _ ↦ hsplit z, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_ite_eq' Finset.univ ((true, true, true, true) : EffectContext) f]
  simp

/-- Cellwise mean individual loss is `2θ_d` in both models: identical mean squared
error in every distance cell. -/
theorem cell_loss_mean (par : Bool) (d : Fin 2) :
    innerExp par d (fun ω ↦ individualLoss (d, ω)) = 2 * cellTheta d := by
  show cellExp par d (fun z ↦ uniformExp (Bool × Bool)
      (fun p ↦ individualLoss (d, (z, p)))) = _
  have hfun : (fun z ↦ uniformExp (Bool × Bool)
      (fun p ↦ individualLoss (d, (z, p)))) = fun z ↦ 2 * (1 - effectMean z) :=
    funext fun z ↦ noise_loss_mean d z
  rw [hfun, cellExp_apply]
  have hsum : ∑ z, parityWeight par z * (2 * (1 - effectMean z)) = 2 := by
    have h1 := parityWeight_sum par
    have h2 := parity_effectMean par
    have : ∑ z, parityWeight par z * (2 * (1 - effectMean z)) =
        2 * ∑ z, parityWeight par z - 2 * ∑ z, parityWeight par z * effectMean z := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun z _ ↦ by ring
    rw [this, h1, h2]; ring
  rw [hsum]
  have h1 : effectMean (true, true, true, true) = 1 := by
    norm_num [effectMean, effectSign_apply]
  rw [h1]
  ring

/-- Cellwise second moment of individual loss: `8θ_d` in model `E`, `(35/4)θ_d` in
model `O`. This is the first summary at which the two models separate. -/
theorem cell_loss_second_moment (par : Bool) (d : Fin 2) :
    innerExp par d (fun ω ↦ individualLoss (d, ω) ^ 2) =
      (if par then 8 else 35 / 4) * cellTheta d := by
  show cellExp par d (fun z ↦ uniformExp (Bool × Bool)
      (fun p ↦ individualLoss (d, (z, p)) ^ 2)) = _
  have hfun : (fun z ↦ uniformExp (Bool × Bool)
      (fun p ↦ individualLoss (d, (z, p)) ^ 2)) = lossSecondMoment :=
    funext fun z ↦ noise_loss_second_moment d z
  rw [hfun, cellExp_apply, parity_lossSecondMoment]
  have hzero : lossSecondMoment (true, true, true, true) = 0 := by
    norm_num [lossSecondMoment, effectMean, effectSign_apply]
  rw [hzero]; ring

/-- Unconditional mean individual loss is `1` in both models. -/
theorem total_loss_mean (par : Bool) : jointExp par individualLoss = 1 := by
  show uniformExp (Fin 2) (fun d ↦ innerExp par d (fun ω ↦ individualLoss (d, ω))) = 1
  have hfun : (fun d ↦ innerExp par d (fun ω ↦ individualLoss (d, ω))) =
      fun d ↦ 2 * cellTheta d := funext fun d ↦ cell_loss_mean par d
  rw [hfun]
  simp [uniformExp_apply, Fin.sum_univ_two, cellTheta]
  norm_num

/-- Unconditional second moment of individual loss: `4` in model `E`, `35/8` in `O`. -/
theorem total_loss_second_moment (par : Bool) :
    jointExp par (fun ω ↦ individualLoss ω ^ 2) = if par then 4 else 35 / 8 := by
  show uniformExp (Fin 2) (fun d ↦ innerExp par d (fun ω ↦ individualLoss (d, ω) ^ 2)) = _
  have hfun : (fun d ↦ innerExp par d (fun ω ↦ individualLoss (d, ω) ^ 2)) =
      fun d ↦ (if par then 8 else 35 / 4) * cellTheta d :=
    funext fun d ↦ cell_loss_second_moment par d
  rw [hfun]
  cases par <;>
    simp [uniformExp_apply, Fin.sum_univ_two, cellTheta] <;> norm_num

/-- Total individual-loss variance: exactly `3` in model `E` and `27/8` in model `O`. -/
theorem total_loss_variance (par : Bool) :
    variance (jointExp par) individualLoss = if par then 3 else 27 / 8 := by
  rw [variance_eq_expect_sq_sub_sq_mean, total_loss_mean, total_loss_second_moment]
  cases par <;> norm_num

/-- Between-cell variance of mean loss is exactly `1/4` in both models. -/
theorem between_cell_variance (par : Bool) :
    variance (uniformExp (Fin 2))
      (fun d ↦ innerExp par d (fun ω ↦ individualLoss (d, ω))) = 1 / 4 := by
  have hfun : (fun d ↦ innerExp par d (fun ω ↦ individualLoss (d, ω))) =
      fun d ↦ 2 * cellTheta d := funext fun d ↦ cell_loss_mean par d
  rw [hfun, variance_eq_expect_sq_sub_sq_mean]
  simp [uniformExp_apply, Fin.sum_univ_two, cellTheta]
  norm_num

/-- The between/within split of the hierarchical loss law, from
`IndividualLossMoments.total_variance`. -/
theorem loss_variance_split (par : Bool) :
    variance (jointExp par) individualLoss =
      uniformExp (Fin 2)
        (fun d ↦ variance (innerExp par d) (fun ω ↦ individualLoss (d, ω))) +
      variance (uniformExp (Fin 2))
        (fun d ↦ innerExp par d (fun ω ↦ individualLoss (d, ω))) := by
  unfold jointExp
  exact total_variance _ _ _

/-- The distance-explainable fraction of individual squared loss. -/
def distanceExplainedLoss (par : Bool) : ℝ :=
  explainableFraction
    (variance (uniformExp (Fin 2))
      (fun d ↦ innerExp par d (fun ω ↦ individualLoss (d, ω))))
    (variance (jointExp par) individualLoss)

/-- **TQ Theorem 8.2.** The two hierarchical context mixtures report
distance-explainable individual-loss fractions `1/12` and `2/27`. -/
theorem fourth_order_loss_obstruction :
    distanceExplainedLoss true = 1 / 12 ∧ distanceExplainedLoss false = 2 / 27 := by
  constructor <;>
    · unfold distanceExplainedLoss explainableFraction Descent.Core.ratio
      rw [between_cell_variance, total_loss_variance]
      norm_num

/-- Cellwise mean score is zero in both models. -/
theorem cell_score_mean (par : Bool) (d : Fin 2) :
    innerExp par d (fun ω ↦ score (d, ω)) = 0 := by
  show cellExp par d (fun z ↦ uniformExp (Bool × Bool)
      (fun p ↦ score (d, (z, p)))) = _
  have hfun : (fun z ↦ uniformExp (Bool × Bool)
      (fun p ↦ score (d, (z, p)))) = fun _ : EffectContext ↦ (0 : ℝ) := by
    funext z
    simp [uniformExp_apply, Fintype.sum_prod_type, score, effectSign_apply]
    norm_num
  rw [hfun, cellExp_apply]
  simp

/-- Cellwise mean outcome is zero in both models. -/
theorem cell_outcome_mean (par : Bool) (d : Fin 2) :
    innerExp par d (fun ω ↦ outcome (d, ω)) = 0 := by
  show cellExp par d (fun z ↦ uniformExp (Bool × Bool)
      (fun p ↦ outcome (d, (z, p)))) = _
  have hfun : (fun z ↦ uniformExp (Bool × Bool)
      (fun p ↦ outcome (d, (z, p)))) = fun _ : EffectContext ↦ (0 : ℝ) := by
    funext z
    simp [uniformExp_apply, Fintype.sum_prod_type, outcome, effectSign_apply]
    ring
  rw [hfun, cellExp_apply]
  simp

/-- Cellwise second moments of score and outcome are both one, and their cellwise
covariance is `1 - θ_d`: every conditional first and second moment of `(S,Y)` is the
same in the two models. -/
theorem cell_second_moments (par : Bool) (d : Fin 2) :
    innerExp par d (fun ω ↦ score (d, ω) ^ 2) = 1 ∧
      innerExp par d (fun ω ↦ outcome (d, ω) ^ 2) = 1 ∧
      innerExp par d (fun ω ↦ score (d, ω) * outcome (d, ω)) = 1 - cellTheta d := by
  refine ⟨?_, ?_, ?_⟩
  · show cellExp par d (fun z ↦ uniformExp (Bool × Bool)
        (fun p ↦ score (d, (z, p)) ^ 2)) = _
    have hfun : (fun z ↦ uniformExp (Bool × Bool)
        (fun p ↦ score (d, (z, p)) ^ 2)) = fun _ : EffectContext ↦ (1 : ℝ) := by
      funext z
      simp [uniformExp_apply, score, effectSign_apply]
    rw [hfun, cellExp_apply, ← Finset.sum_mul, parityWeight_sum]
    ring
  · show cellExp par d (fun z ↦ uniformExp (Bool × Bool)
        (fun p ↦ outcome (d, (z, p)) ^ 2)) = _
    have hfun : (fun z ↦ uniformExp (Bool × Bool)
        (fun p ↦ outcome (d, (z, p)) ^ 2)) = fun _ : EffectContext ↦ (1 : ℝ) := by
      funext z
      have hb := sqrt_residual_sq z
      simp only [uniformExp_apply, Fintype.sum_prod_type, Fintype.sum_bool, outcome,
        effectSign_apply, Fintype.card_prod, Fintype.card_bool]
      norm_num
      linear_combination hb
    rw [hfun, cellExp_apply, ← Finset.sum_mul, parityWeight_sum]
    ring
  · show cellExp par d (fun z ↦ uniformExp (Bool × Bool)
        (fun p ↦ score (d, (z, p)) * outcome (d, (z, p)))) = _
    have hfun : (fun z ↦ uniformExp (Bool × Bool)
        (fun p ↦ score (d, (z, p)) * outcome (d, (z, p)))) = effectMean := by
      funext z
      simp only [uniformExp_apply, Fintype.sum_prod_type, Fintype.sum_bool, outcome,
        score, effectSign_apply, Fintype.card_prod, Fintype.card_bool]
      norm_num
      ring
    rw [hfun, cellExp_apply, parity_effectMean]
    norm_num [effectMean, effectSign_apply]

/-- The pooled within-cell squared correlation is `(1 - θ_d)^2` and the expected
squared correlation given the sampled effect state is `1 - 3θ_d/4`: both summaries
agree across the two models, at every cell. -/
theorem cell_squared_correlations (par : Bool) (d : Fin 2) :
    innerExp par d (fun ω ↦ score (d, ω) * outcome (d, ω)) ^ 2 = (1 - cellTheta d) ^ 2 ∧
      cellExp par d (fun z ↦ effectMean z ^ 2) = 1 - 3 * cellTheta d / 4 := by
  refine ⟨by rw [(cell_second_moments par d).2.2], ?_⟩
  rw [cellExp_apply, parity_effectMean_sq]
  norm_num [effectMean, effectSign_apply]
  ring

end

end Descent.Portability.FourthOrderLossObstruction
