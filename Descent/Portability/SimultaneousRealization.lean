/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AlignmentFactorization
import Descent.Portability.TraitPortabilityRange

assert_below Descent.Decision Descent.Program

/-!
# One genotype law carrying an arbitrary curve and a tunable loss-explainability

TQ Theorem 8.1 and its model (8.1).  Two independent fair scored genotype signs and a
finite cell law carry, for a fixed heritability `H ∈ (0,1)` and an arbitrary prescribed
cellwise curve `q(d) ∈ [0,H]`, a target phenotype

`Y = √q(D) X₁ + √(H − q(D)) X₂ + ε`,  `S = √H X₁`,

whose cellwise outcome variance is `1`, whose cellwise genotype-explained fraction is
`H`, and whose cellwise squared correlation with the deployed score is exactly `q(d)`
(TQ Theorem 3.3 equation (3.6); the same statement as UPT Theorem 4.2 on this
background).  Those three conclusions are stated through the `AlignmentFactorization`
objects, so the general factorization `q = H ρ²` applies to them verbatim.

Nothing in the genotype law, the score, or the conditional first two moments of the
noise depends on the noise *shape*; only the fourth moment does.  This stage of the
module proves the curve half.  The loss half -- the exact attainable interval
`(0, B/(B+W₀)]` for the distance-explained fraction of individual squared loss -- is
built on it.

Builds on `IndividualLossMoments.mixture`, `Portability.uniformExp`,
`AlignmentFactorization.scoreAccuracy`, `AlignmentFactorization.genotypeExplainedFraction`
and `TraitPortabilityRange.sign`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SimultaneousRealization

open Foundations IndividualLossMoments AlignmentFactorization

open TraitPortabilityRange (sign)

noncomputable section

variable {D Ω : Type*}

/-- The within-cell law: two independent fair scored genotype signs together with an
independent environmental noise law `N`.  The genotype half is the same for every
prescribed curve, every heritability and every noise law. -/
def cellLaw (N : ExpFunctional Ω) : ExpFunctional ((Bool × Bool) × Ω) :=
  mixture (uniformExp (Bool × Bool)) (fun _ ↦ N)

/-- The within-cell law is the genotype expectation of the noise expectation. -/
theorem cellLaw_eval (N : ExpFunctional Ω) (f : (Bool × Bool) × Ω → ℝ) :
    cellLaw N f = uniformExp (Bool × Bool) (fun g ↦ N (fun ω ↦ f (g, ω))) := rfl

/-- The within-cell law read as the mixture the alignment theory is stated over. -/
theorem cellLaw_def (N : ExpFunctional Ω) :
    cellLaw N = mixture (uniformExp (Bool × Bool)) (fun _ ↦ N) := rfl

/-- The deployed source-trained score `S = √H X₁`, a function of the genotype alone. -/
def deployedScore (H : ℝ) : Bool × Bool → ℝ := fun g ↦ Real.sqrt H * sign g.1

/-- The target phenotype in cell `d`, TQ equation (8.1). -/
def cellPhenotype (H : ℝ) (q : D → ℝ) (e : Ω → ℝ) (d : D) : (Bool × Bool) × Ω → ℝ :=
  fun z ↦ Real.sqrt (q d) * sign z.1.1 + Real.sqrt (H - q d) * sign z.1.2 + e z.2

/-- Residual coefficient `a(d) = √q(d) − √H`. -/
def coeffA (H : ℝ) (q : D → ℝ) (d : D) : ℝ := Real.sqrt (q d) - Real.sqrt H

/-- Residual coefficient `b(d) = √(H − q(d))`. -/
def coeffB (H : ℝ) (q : D → ℝ) (d : D) : ℝ := Real.sqrt (H - q d)

/-- The individual prediction residual `Y − S`, on the joint cell-genotype-noise space. -/
def cellResidual (H : ℝ) (q : D → ℝ) (e : Ω → ℝ) : D × ((Bool × Bool) × Ω) → ℝ :=
  fun z ↦ cellPhenotype H q e z.1 z.2 - liftGenotype (deployedScore H) z.2

/-- The residual is the two-contrast form the moment computations use. -/
theorem cellResidual_eq (H : ℝ) (q : D → ℝ) (e : Ω → ℝ) (d : D) (z : (Bool × Bool) × Ω) :
    cellResidual H q e (d, z)
      = coeffA H q d * sign z.1.1 + coeffB H q d * sign z.1.2 + e z.2 := by
  unfold cellResidual cellPhenotype liftGenotype deployedScore coeffA coeffB
  ring

/-- Shifting an observable by a constant, first order. -/
theorem shift_one (N : ExpFunctional Ω) (e : Ω → ℝ) (u : ℝ) :
    N (fun ω ↦ u + e ω) = u + N e := by
  have hsplit : (fun ω ↦ u + e ω) = (fun _ : Ω ↦ u) + e := by
    funext ω
    simp only [Pi.add_apply]
  rw [hsplit, N.add_eval, ExpFunctional.eval_const]

/-- A constant multiple of a shifted observable. -/
theorem shift_mul (N : ExpFunctional Ω) (e : Ω → ℝ) (c u : ℝ) :
    N (fun ω ↦ c * (u + e ω)) = c * u + c * N e := by
  have hsplit : (fun ω ↦ c * (u + e ω)) = (fun _ : Ω ↦ c * u) + (c • e) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit, N.add_eval, N.smul_eval, ExpFunctional.eval_const]

/-- Shifting an observable by a constant, second order. -/
theorem shift_sq (N : ExpFunctional Ω) (e : Ω → ℝ) (u : ℝ) :
    N (fun ω ↦ (u + e ω) ^ 2)
      = u ^ 2 + 2 * u * N e + N (fun ω ↦ e ω ^ 2) := by
  have hsplit : (fun ω ↦ (u + e ω) ^ 2)
      = (fun _ : Ω ↦ u ^ 2) + ((2 * u) • e) + (fun ω ↦ e ω ^ 2) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit, N.add_eval, N.add_eval, N.smul_eval, ExpFunctional.eval_const]

/-- Shifting an observable by a constant, fourth order. -/
theorem shift_pow_four (N : ExpFunctional Ω) (e : Ω → ℝ) (u : ℝ) :
    N (fun ω ↦ (u + e ω) ^ 4)
      = u ^ 4 + 4 * u ^ 3 * N e + 6 * u ^ 2 * N (fun ω ↦ e ω ^ 2)
        + 4 * u * N (fun ω ↦ e ω ^ 3) + N (fun ω ↦ e ω ^ 4) := by
  have hsplit : (fun ω ↦ (u + e ω) ^ 4)
      = (fun _ : Ω ↦ u ^ 4) + ((4 * u ^ 3) • e) + ((6 * u ^ 2) • fun ω ↦ e ω ^ 2)
        + ((4 * u) • fun ω ↦ e ω ^ 3) + (fun ω ↦ e ω ^ 4) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit, N.add_eval, N.add_eval, N.add_eval, N.add_eval, N.smul_eval, N.smul_eval,
    N.smul_eval, ExpFunctional.eval_const]

/-- The mean of a two-contrast genotype observable is zero. -/
theorem genotype_contrast_mean (A Bv : ℝ) :
    uniformExp (Bool × Bool) (fun g ↦ A * sign g.1 + Bv * sign g.2) = 0 := by
  norm_num [uniformExp_apply, Fintype.sum_prod_type, Fintype.sum_bool, sign]
  ring

/-- The variance of a two-contrast genotype observable is the sum of squared
coefficients: the two scored signs are uncorrelated and standardized. -/
theorem genotype_contrast_variance (A Bv : ℝ) :
    variance (uniformExp (Bool × Bool)) (fun g ↦ A * sign g.1 + Bv * sign g.2)
      = A ^ 2 + Bv ^ 2 := by
  rw [variance_eq_expect_sq_sub_sq_mean, genotype_contrast_mean]
  norm_num [uniformExp_apply, Fintype.sum_prod_type, Fintype.sum_bool, sign]
  ring

/-- The covariance of the first scored sign with a two-contrast observable picks out its
own coefficient. -/
theorem genotype_contrast_covariance (c A Bv : ℝ) :
    covariance (uniformExp (Bool × Bool)) (fun g ↦ c * sign g.1)
        (fun g ↦ A * sign g.1 + Bv * sign g.2) = c * A := by
  rw [covariance_eq_expect_mul_sub_means, genotype_contrast_mean]
  norm_num [uniformExp_apply, Fintype.sum_prod_type, Fintype.sum_bool, sign]
  ring

/-- The variance of the deployed score is the heritability, on every noise law. -/
theorem deployedScore_variance (H : ℝ) (hH : 0 ≤ H) :
    variance (uniformExp (Bool × Bool)) (deployedScore H) = H := by
  have hzero : deployedScore H = fun g : Bool × Bool ↦ Real.sqrt H * sign g.1 + 0 * sign g.2 := by
    funext g
    unfold deployedScore
    ring
  rw [hzero, genotype_contrast_variance, Real.sq_sqrt hH]
  ring

/-- **The conditional mean of a two-contrast phenotype.** -/
theorem contrast_first_moment (N : ExpFunctional Ω) (e : Ω → ℝ) (A Bv : ℝ) :
    cellLaw N (fun z ↦ A * sign z.1.1 + Bv * sign z.1.2 + e z.2) = N e := by
  rw [cellLaw_eval]
  have hinner : (fun g : Bool × Bool ↦ N (fun ω ↦ A * sign g.1 + Bv * sign g.2 + e ω))
      = fun g : Bool × Bool ↦ (A * sign g.1 + Bv * sign g.2) + N e :=
    funext fun g ↦ shift_one N e _
  rw [hinner]
  norm_num [uniformExp_apply, Fintype.sum_prod_type, Fintype.sum_bool, sign]
  ring

/-- **The exact conditional second moment of a two-contrast phenotype.**  No hypothesis
on the noise law: the genotype signs are orthogonal and standardized, so only the noise
second moment enters. -/
theorem contrast_second_moment (N : ExpFunctional Ω) (e : Ω → ℝ) (A Bv : ℝ) :
    cellLaw N (fun z ↦ (A * sign z.1.1 + Bv * sign z.1.2 + e z.2) ^ 2)
      = A ^ 2 + Bv ^ 2 + N (fun ω ↦ e ω ^ 2) := by
  rw [cellLaw_eval]
  have hinner : (fun g : Bool × Bool ↦ N (fun ω ↦ (A * sign g.1 + Bv * sign g.2 + e ω) ^ 2))
      = fun g : Bool × Bool ↦ (A * sign g.1 + Bv * sign g.2) ^ 2
          + 2 * (A * sign g.1 + Bv * sign g.2) * N e + N (fun ω ↦ e ω ^ 2) :=
    funext fun g ↦ shift_sq N e _
  rw [hinner]
  norm_num [uniformExp_apply, Fintype.sum_prod_type, Fintype.sum_bool, sign]
  ring

/-- **The exact conditional fourth moment of a two-contrast phenotype.**  The noise
third moment drops out because both contrasts are symmetric; the noise fourth moment
enters additively.  This is the coordinate TQ Theorem 8.1 tunes. -/
theorem contrast_fourth_moment (N : ExpFunctional Ω) (e : Ω → ℝ) (A Bv : ℝ) :
    cellLaw N (fun z ↦ (A * sign z.1.1 + Bv * sign z.1.2 + e z.2) ^ 4)
      = (A ^ 2 + Bv ^ 2) ^ 2 + 4 * A ^ 2 * Bv ^ 2
        + 6 * (A ^ 2 + Bv ^ 2) * N (fun ω ↦ e ω ^ 2) + N (fun ω ↦ e ω ^ 4) := by
  rw [cellLaw_eval]
  have hinner : (fun g : Bool × Bool ↦ N (fun ω ↦ (A * sign g.1 + Bv * sign g.2 + e ω) ^ 4))
      = fun g : Bool × Bool ↦ (A * sign g.1 + Bv * sign g.2) ^ 4
          + 4 * (A * sign g.1 + Bv * sign g.2) ^ 3 * N e
          + 6 * (A * sign g.1 + Bv * sign g.2) ^ 2 * N (fun ω ↦ e ω ^ 2)
          + 4 * (A * sign g.1 + Bv * sign g.2) * N (fun ω ↦ e ω ^ 3)
          + N (fun ω ↦ e ω ^ 4) :=
    funext fun g ↦ shift_pow_four N e _
  rw [hinner]
  norm_num [uniformExp_apply, Fintype.sum_prod_type, Fintype.sum_bool, sign]
  ring

/-- **The cross moment of the deployed score with the phenotype** picks out the
coefficient of the scored sign the score is built from, and nothing else. -/
theorem contrast_score_cross (N : ExpFunctional Ω) (e : Ω → ℝ) (c A Bv : ℝ) :
    cellLaw N (fun z ↦ c * sign z.1.1 * (A * sign z.1.1 + Bv * sign z.1.2 + e z.2))
      = c * A := by
  rw [cellLaw_eval]
  have hinner : (fun g : Bool × Bool ↦
      N (fun ω ↦ c * sign g.1 * (A * sign g.1 + Bv * sign g.2 + e ω)))
      = fun g : Bool × Bool ↦ c * sign g.1 * (A * sign g.1 + Bv * sign g.2)
          + c * sign g.1 * N e :=
    funext fun g ↦ shift_mul N e _ _
  rw [hinner]
  norm_num [uniformExp_apply, Fintype.sum_prod_type, Fintype.sum_bool, sign]
  ring

/-- **The genotype regression function of the target phenotype.**  Conditioning on the
genotype removes exactly the environmental term. -/
theorem cell_regression_function (N : ExpFunctional Ω) (H : ℝ) (q : D → ℝ) (e : Ω → ℝ)
    (d : D) (hmean : N e = 0) :
    regressionFunction (fun _ : Bool × Bool ↦ N) (cellPhenotype H q e d)
      = fun g : Bool × Bool ↦
        Real.sqrt (q d) * sign g.1 + Real.sqrt (H - q d) * sign g.2 := by
  funext g
  show N (fun ω ↦ (Real.sqrt (q d) * sign g.1 + Real.sqrt (H - q d) * sign g.2) + e ω)
    = Real.sqrt (q d) * sign g.1 + Real.sqrt (H - q d) * sign g.2
  rw [shift_one, hmean]
  ring

/-- **The cellwise outcome variance is exactly one**, whatever the prescribed curve and
whatever the noise shape with the stated first two moments. -/
theorem cellPhenotype_variance (N : ExpFunctional Ω) (H : ℝ) (q : D → ℝ) (e : Ω → ℝ)
    (d : D) (hq0 : 0 ≤ q d) (hqH : q d ≤ H) (hmean : N e = 0)
    (hvar : N (fun ω ↦ e ω ^ 2) = 1 - H) :
    variance (cellLaw N) (cellPhenotype H q e d) = 1 := by
  have hqd : (0:ℝ) ≤ H - q d := by linarith
  have hmean' : cellLaw N (cellPhenotype H q e d) = 0 := by
    unfold cellPhenotype
    rw [contrast_first_moment, hmean]
  rw [variance_eq_expect_sq_sub_sq_mean, hmean']
  have hsq : (fun z : (Bool × Bool) × Ω ↦ cellPhenotype H q e d z ^ 2)
      = fun z : (Bool × Bool) × Ω ↦
        (Real.sqrt (q d) * sign z.1.1 + Real.sqrt (H - q d) * sign z.1.2 + e z.2) ^ 2 := rfl
  rw [hsq, contrast_second_moment, hvar, Real.sq_sqrt hq0, Real.sq_sqrt hqd]
  ring

/-- **The cellwise genotype-explained variance fraction is exactly `H`**, for every
prescribed curve.  TQ Theorem 3.3 equation (3.6), second conclusion. -/
theorem cell_genotype_fraction (N : ExpFunctional Ω) (H : ℝ) (q : D → ℝ) (e : Ω → ℝ)
    (d : D) (hq0 : 0 ≤ q d) (hqH : q d ≤ H) (hmean : N e = 0)
    (hvar : N (fun ω ↦ e ω ^ 2) = 1 - H) :
    genotypeExplainedFraction (uniformExp (Bool × Bool)) (fun _ ↦ N)
        (cellPhenotype H q e d) = H := by
  have hqd : (0:ℝ) ≤ H - q d := by linarith
  unfold genotypeExplainedFraction explainableFraction Descent.Core.ratio
  rw [cell_regression_function N H q e d hmean, genotype_contrast_variance,
    Real.sq_sqrt hq0, Real.sq_sqrt hqd, ← cellLaw_def,
    cellPhenotype_variance N H q e d hq0 hqH hmean hvar]
  ring

/-- **The cellwise squared correlation with the deployed score is exactly the prescribed
`q(d)`.**  TQ Theorem 3.3 equation (3.6), third conclusion, on a genotype law and a
source-trained score that do not depend on the prescribed curve. -/
theorem cell_score_accuracy (N : ExpFunctional Ω) (H : ℝ) (q : D → ℝ) (e : Ω → ℝ)
    (d : D) (hH0 : 0 < H) (hq0 : 0 ≤ q d) (hqH : q d ≤ H) (hmean : N e = 0)
    (hvar : N (fun ω ↦ e ω ^ 2) = 1 - H) :
    scoreAccuracy (uniformExp (Bool × Bool)) (fun _ ↦ N) (deployedScore H)
        (cellPhenotype H q e d) = q d := by
  unfold scoreAccuracy
  rw [mixture_covariance_liftGenotype, cell_regression_function N H q e d hmean,
    ← cellLaw_def, cellPhenotype_variance N H q e d hq0 hqH hmean hvar,
    deployedScore_variance H hH0.le]
  unfold deployedScore
  rw [genotype_contrast_covariance, mul_pow, Real.sq_sqrt hH0.le, Real.sq_sqrt hq0]
  field_simp

/-- **TQ Theorem 3.3 / model (8.1): the prescribed curve is realized exactly, on a fixed
genotype law, at fixed heritability, with the same source-trained score.**  All three
conclusions of equation (3.6) at once. -/
theorem fixed_background_curve_realized (N : ExpFunctional Ω) (H : ℝ) (q : D → ℝ)
    (e : Ω → ℝ) (d : D) (hH0 : 0 < H) (hq0 : 0 ≤ q d) (hqH : q d ≤ H)
    (hmean : N e = 0) (hvar : N (fun ω ↦ e ω ^ 2) = 1 - H) :
    variance (cellLaw N) (cellPhenotype H q e d) = 1 ∧
      genotypeExplainedFraction (uniformExp (Bool × Bool)) (fun _ ↦ N)
        (cellPhenotype H q e d) = H ∧
      scoreAccuracy (uniformExp (Bool × Bool)) (fun _ ↦ N) (deployedScore H)
        (cellPhenotype H q e d) = q d :=
  ⟨cellPhenotype_variance N H q e d hq0 hqH hmean hvar,
    cell_genotype_fraction N H q e d hq0 hqH hmean hvar,
    cell_score_accuracy N H q e d hH0 hq0 hqH hmean hvar⟩

/-! ### The individual-loss half -/

/-- `m(d) = E[L ∣ D = d] = 1 + H − 2√(H q(d))`, TQ equation (8.2). -/
def lossMean (H : ℝ) (q : D → ℝ) : D → ℝ :=
  fun d ↦ 1 + H - 2 * Real.sqrt H * Real.sqrt (q d)

/-- `B = Var(m(D))`, the between-cell variance of the mean individual squared loss. -/
def lossMeanVariance (E : ExpFunctional D) (H : ℝ) (q : D → ℝ) : ℝ :=
  variance E (lossMean H q)

/-- `W₀ = E[4a(D)²b(D)² + 4(1−H)(a(D)² + b(D)²)]`, the mean within-cell loss variance
that the genotype contrasts force whatever the noise shape. -/
def minimalWithinVariance (E : ExpFunctional D) (H : ℝ) (q : D → ℝ) : ℝ :=
  E (fun d ↦ 4 * coeffA H q d ^ 2 * coeffB H q d ^ 2
    + 4 * (1 - H) * (coeffA H q d ^ 2 + coeffB H q d ^ 2))

/-- The full law: distance cells, genotype, environmental noise. -/
def fullLaw (E : ExpFunctional D) (N : ExpFunctional Ω) :
    ExpFunctional (D × ((Bool × Bool) × Ω)) :=
  mixture E (fun _ ↦ cellLaw N)

/-- `η_D`: the fraction of individual squared-loss variance that the distance cell
explains. -/
def lossExplainedFraction (E : ExpFunctional D) (N : ExpFunctional Ω) (H : ℝ)
    (q : D → ℝ) (e : Ω → ℝ) : ℝ :=
  explainableFraction
    (variance E (fun d ↦ cellLaw N (fun z ↦ cellResidual H q e (d, z) ^ 2)))
    (variance (fullLaw E N) (fun z ↦ cellResidual H q e z ^ 2))

/-- Adding a constant inside an expectation. -/
theorem eval_add_const (E : ExpFunctional D) (f : D → ℝ) (c : ℝ) :
    E (fun d ↦ f d + c) = E f + c := by
  have hsplit : (fun d ↦ f d + c) = f + (fun _ : D ↦ c) := by
    funext d
    simp only [Pi.add_apply]
  rw [hsplit, E.add_eval, ExpFunctional.eval_const]

/-- **TQ equation (8.2): the exact conditional mean individual loss.** -/
theorem cell_loss_mean (N : ExpFunctional Ω) (H : ℝ) (q : D → ℝ) (e : Ω → ℝ) (d : D)
    (hH : 0 ≤ H) (hq0 : 0 ≤ q d) (hqH : q d ≤ H)
    (hvar : N (fun ω ↦ e ω ^ 2) = 1 - H) :
    cellLaw N (fun z ↦ cellResidual H q e (d, z) ^ 2) = lossMean H q d := by
  have hqq : Real.sqrt (q d) ^ 2 = q d := Real.sq_sqrt hq0
  have hHH : Real.sqrt H ^ 2 = H := Real.sq_sqrt hH
  have hHq : Real.sqrt (H - q d) ^ 2 = H - q d :=
    Real.sq_sqrt (by linarith)
  have h2 : (fun z : (Bool × Bool) × Ω ↦ cellResidual H q e (d, z) ^ 2)
      = fun z : (Bool × Bool) × Ω ↦
        (coeffA H q d * sign z.1.1 + coeffB H q d * sign z.1.2 + e z.2) ^ 2 := by
    funext z
    rw [cellResidual_eq]
  rw [h2, contrast_second_moment, hvar]
  unfold coeffA coeffB lossMean
  linear_combination hqq + hHH + hHq

/-- **The exact conditional variance of individual squared loss in one cell.**  Only the
noise second and fourth moments enter; the noise shape is otherwise free.  This is the
one coordinate TQ Theorem 8.1 moves. -/
theorem cell_loss_within (N : ExpFunctional Ω) (H : ℝ) (q : D → ℝ) (e : Ω → ℝ) (d : D) :
    cellLaw N (fun z ↦ cellResidual H q e (d, z) ^ 4)
        - cellLaw N (fun z ↦ cellResidual H q e (d, z) ^ 2) ^ 2
      = 4 * coeffA H q d ^ 2 * coeffB H q d ^ 2
        + 4 * N (fun ω ↦ e ω ^ 2) * (coeffA H q d ^ 2 + coeffB H q d ^ 2)
        + (N (fun ω ↦ e ω ^ 4) - N (fun ω ↦ e ω ^ 2) ^ 2) := by
  have h4 : (fun z : (Bool × Bool) × Ω ↦ cellResidual H q e (d, z) ^ 4)
      = fun z : (Bool × Bool) × Ω ↦
        (coeffA H q d * sign z.1.1 + coeffB H q d * sign z.1.2 + e z.2) ^ 4 := by
    funext z
    rw [cellResidual_eq]
  have h2 : (fun z : (Bool × Bool) × Ω ↦ cellResidual H q e (d, z) ^ 2)
      = fun z : (Bool × Bool) × Ω ↦
        (coeffA H q d * sign z.1.1 + coeffB H q d * sign z.1.2 + e z.2) ^ 2 := by
    funext z
    rw [cellResidual_eq]
  rw [h4, h2, contrast_fourth_moment, contrast_second_moment]
  ring

/-- The between-cell variance of individual loss is `B`. -/
theorem loss_between_variance (E : ExpFunctional D) (N : ExpFunctional Ω) (H : ℝ)
    (q : D → ℝ) (e : Ω → ℝ) (hH : 0 ≤ H) (hq0 : ∀ d, 0 ≤ q d) (hqH : ∀ d, q d ≤ H)
    (hvar : N (fun ω ↦ e ω ^ 2) = 1 - H) :
    variance E (fun d ↦ cellLaw N (fun z ↦ cellResidual H q e (d, z) ^ 2))
      = lossMeanVariance E H q := by
  have hfun : (fun d ↦ cellLaw N (fun z ↦ cellResidual H q e (d, z) ^ 2)) = lossMean H q :=
    funext fun d ↦ cell_loss_mean N H q e d hH (hq0 d) (hqH d) hvar
  unfold lossMeanVariance
  rw [hfun]

/-- **The exact total variance of individual squared loss**: between-cell `B`, plus the
forced within-cell floor `W₀`, plus the noise fourth-moment excess. -/
theorem loss_total_variance (E : ExpFunctional D) (N : ExpFunctional Ω) (H : ℝ)
    (q : D → ℝ) (e : Ω → ℝ) (hH : 0 ≤ H) (hq0 : ∀ d, 0 ≤ q d) (hqH : ∀ d, q d ≤ H)
    (hvar : N (fun ω ↦ e ω ^ 2) = 1 - H) :
    variance (fullLaw E N) (fun z ↦ cellResidual H q e z ^ 2)
      = minimalWithinVariance E H q + (N (fun ω ↦ e ω ^ 4) - (1 - H) ^ 2)
        + lossMeanVariance E H q := by
  have hint : (fun d ↦ cellLaw N (fun z ↦ cellResidual H q e (d, z) ^ 4)
        - cellLaw N (fun z ↦ cellResidual H q e (d, z) ^ 2) ^ 2)
      = fun d ↦ (4 * coeffA H q d ^ 2 * coeffB H q d ^ 2
          + 4 * (1 - H) * (coeffA H q d ^ 2 + coeffB H q d ^ 2))
        + (N (fun ω ↦ e ω ^ 4) - (1 - H) ^ 2) := by
    funext d
    rw [cell_loss_within, hvar]
  unfold minimalWithinVariance
  have hfull : fullLaw E N = mixture E (fun _ : D ↦ cellLaw N) := rfl
  rw [hfull, squared_loss_total, hint, eval_add_const,
    loss_between_variance E N H q e hH hq0 hqH hvar]

/-- Cauchy-Schwarz: no law's fourth moment is below the square of its second. -/
theorem noise_fourth_moment_ge (N : ExpFunctional Ω) (e : Ω → ℝ) :
    N (fun ω ↦ e ω ^ 2) ^ 2 ≤ N (fun ω ↦ e ω ^ 4) := by
  have h := ExpFunctional.cauchy_schwarz N (fun _ ↦ (1:ℝ)) (fun ω ↦ e ω ^ 2)
  have h1 : (fun ω : Ω ↦ (1:ℝ) * e ω ^ 2) = fun ω ↦ e ω ^ 2 := by
    funext ω
    ring
  have h2 : (fun _ : Ω ↦ (1:ℝ) ^ 2) = fun _ : Ω ↦ (1:ℝ) := by
    funext ω
    ring
  have h3 : (fun ω : Ω ↦ (e ω ^ 2) ^ 2) = fun ω ↦ e ω ^ 4 := by
    funext ω
    ring
  rw [h1, h2, h3, ExpFunctional.eval_const, one_mul] at h
  exact h

/-- The forced within-cell floor is nonnegative. -/
theorem minimalWithinVariance_nonneg (E : ExpFunctional D) (H : ℝ) (q : D → ℝ)
    (hH1 : H ≤ 1) : 0 ≤ minimalWithinVariance E H q := by
  have h1 : (0:ℝ) ≤ 1 - H := by linarith
  refine E.nonneg_eval _ fun d ↦ ?_
  nlinarith [sq_nonneg (coeffA H q d), sq_nonneg (coeffB H q d),
    mul_nonneg (sq_nonneg (coeffA H q d)) (sq_nonneg (coeffB H q d)),
    mul_nonneg h1 (sq_nonneg (coeffA H q d)), mul_nonneg h1 (sq_nonneg (coeffB H q d))]

/-- **The exact loss-explainability of the model**, for every admissible noise law. -/
theorem lossExplainedFraction_eq (E : ExpFunctional D) (N : ExpFunctional Ω) (H : ℝ)
    (q : D → ℝ) (e : Ω → ℝ) (hH : 0 ≤ H) (hq0 : ∀ d, 0 ≤ q d) (hqH : ∀ d, q d ≤ H)
    (hvar : N (fun ω ↦ e ω ^ 2) = 1 - H) :
    lossExplainedFraction E N H q e
      = lossMeanVariance E H q
        / (minimalWithinVariance E H q + (N (fun ω ↦ e ω ^ 4) - (1 - H) ^ 2)
            + lossMeanVariance E H q) := by
  unfold lossExplainedFraction explainableFraction Descent.Core.ratio
  rw [loss_between_variance E N H q e hH hq0 hqH hvar,
    loss_total_variance E N H q e hH hq0 hqH hvar]

/-- **TQ Theorem 8.1, the bound half: `0 < η_D ≤ B/(B+W₀)` for every admissible noise
shape**, not just for the explicit family.  The upper endpoint is the noise fourth
moment at its Cauchy-Schwarz floor. -/
theorem loss_fraction_bounds (E : ExpFunctional D) (N : ExpFunctional Ω) (H : ℝ)
    (q : D → ℝ) (e : Ω → ℝ) (hH : 0 ≤ H) (hH1 : H ≤ 1) (hq0 : ∀ d, 0 ≤ q d)
    (hqH : ∀ d, q d ≤ H) (hvar : N (fun ω ↦ e ω ^ 2) = 1 - H)
    (hB : 0 < lossMeanVariance E H q) :
    0 < lossExplainedFraction E N H q e ∧
      lossExplainedFraction E N H q e
        ≤ lossMeanVariance E H q
          / (lossMeanVariance E H q + minimalWithinVariance E H q) := by
  have hW : 0 ≤ minimalWithinVariance E H q := minimalWithinVariance_nonneg E H q hH1
  have h4 : (1 - H) ^ 2 ≤ N (fun ω ↦ e ω ^ 4) := by
    have hcs := noise_fourth_moment_ge N e
    rw [hvar] at hcs
    exact hcs
  rw [lossExplainedFraction_eq E N H q e hH hq0 hqH hvar]
  refine ⟨div_pos hB (by linarith), ?_⟩
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

end

end Descent.Portability.SimultaneousRealization
