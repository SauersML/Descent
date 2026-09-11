/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AlignmentFactorization
import Descent.Portability.TraitPortabilityRange
import Descent.Portability.NonaffineRepair

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

## Empirical status

None. The bodies here are algebra: a construction exhibits a law with prescribed moments, and
asserts nothing about any population.  What carries an empirical status is a named
quantity in a subsystem module asserting that this algebra computes something
measurable, and such names keep their own docstrings, regimes and ledger rows.
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

/-! ### The explicit noise family and the sharp interval -/

/-- The three-point weights `(p/2, 1−p, p/2)` of the explicit noise family. -/
def spikeWeights (p : ℝ) : Fin 3 → ℝ := ![p / 2, 1 - p, p / 2]

/-- The three-point sign pattern of the explicit noise family. -/
def spikeSign : Fin 3 → ℝ := ![-1, 0, 1]

/-- The noise sign pattern is the symmetric three-point score of
`NonaffineRepair.rademacherScore`: one shape, used there as a score and here as a
noise carrier. -/
theorem spikeSign_eq_rademacherScore : spikeSign = NonaffineRepair.rademacherScore := rfl

/-- **The explicit noise family of TQ Theorem 8.1**: mass `1 − p` at zero and `p/2` at
each spike.  Its mean and variance are the same for every `p`; only its fourth moment
moves. -/
def spikeLaw (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) : ExpFunctional (Fin 3) :=
  weightedExp (spikeWeights p)
    (by
      intro i
      fin_cases i
      · show (0:ℝ) ≤ p / 2
        linarith
      · show (0:ℝ) ≤ 1 - p
        linarith
      · show (0:ℝ) ≤ p / 2
        linarith)
    (by
      simp only [spikeWeights, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring)

/-- The noise values `ε = √((1−H)/p) · (−1, 0, 1)`. -/
def spikeValue (H p : ℝ) : Fin 3 → ℝ := fun i ↦ Real.sqrt ((1 - H) / p) * spikeSign i

/-- The explicit noise law evaluated on an arbitrary observable. -/
theorem spike_eval (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (f : Fin 3 → ℝ) :
    spikeLaw p hp hp1 f = p / 2 * f 0 + (1 - p) * f 1 + p / 2 * f 2 := by
  simp only [spikeLaw, weightedExp_apply, spikeWeights, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

/-- The spike magnitude is calibrated so that the noise variance is `1 − H` for every
`p`: the model's conditional second moments are untouched by the shape parameter. -/
theorem spike_scale (H p : ℝ) (hp : 0 < p) (hH : H ≤ 1) :
    p * Real.sqrt ((1 - H) / p) ^ 2 = 1 - H := by
  have hpne : p ≠ 0 := ne_of_gt hp
  have hnn : (0:ℝ) ≤ (1 - H) / p := div_nonneg (by linarith) hp.le
  rw [Real.sq_sqrt hnn]
  field_simp

/-- The explicit noise family has mean zero. -/
theorem spike_mean (H p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    spikeLaw p hp hp1 (spikeValue H p) = 0 := by
  rw [spike_eval]
  simp only [spikeValue, spikeSign, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The explicit noise family has variance `1 − H`, for every shape parameter. -/
theorem spike_second_moment (H p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hH : H ≤ 1) :
    spikeLaw p hp hp1 (fun i ↦ spikeValue H p i ^ 2) = 1 - H := by
  have hps := spike_scale H p hp hH
  rw [spike_eval]
  simp only [spikeValue, spikeSign, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  linear_combination hps

/-- The explicit noise family has fourth moment `(1 − H)²/p`: the one coordinate that
the shape parameter moves, and it sweeps `[(1−H)², ∞)`. -/
theorem spike_fourth_moment (H p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hH : H ≤ 1) :
    spikeLaw p hp hp1 (fun i ↦ spikeValue H p i ^ 4) = (1 - H) ^ 2 / p := by
  have hpne : p ≠ 0 := ne_of_gt hp
  have hps := spike_scale H p hp hH
  rw [spike_eval, eq_div_iff hpne]
  simp only [spikeValue, spikeSign, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  linear_combination (p * Real.sqrt ((1 - H) / p) ^ 2 + (1 - H)) * hps

/-- **TQ equation (8.4): the exact loss-explainability of the explicit family.** -/
theorem spike_loss_fraction (E : ExpFunctional D) (H : ℝ) (q : D → ℝ) (p : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hH : 0 ≤ H) (hH1 : H ≤ 1) (hq0 : ∀ d, 0 ≤ q d)
    (hqH : ∀ d, q d ≤ H) :
    lossExplainedFraction E (spikeLaw p hp hp1) H q (spikeValue H p)
      = lossMeanVariance E H q
        / (lossMeanVariance E H q + minimalWithinVariance E H q
            + (1 - H) ^ 2 * (p⁻¹ - 1)) := by
  rw [lossExplainedFraction_eq E (spikeLaw p hp hp1) H q (spikeValue H p) hH hq0 hqH
      (spike_second_moment H p hp hp1 hH1),
    spike_fourth_moment H p hp hp1 hH1]
  congr 1
  ring

/-- **The prescribed explainability leaves nonnegative slack in the loss budget.**
`η ≤ B/(B+W₀)` is exactly `B + W₀ ≤ B/η`, which is what makes the shape parameter
admissible. -/
theorem lossBudget_slack (E : ExpFunctional D) (H : ℝ) (q : D → ℝ) (eta : ℝ)
    (hW : 0 ≤ minimalWithinVariance E H q) (hB : 0 < lossMeanVariance E H q)
    (heta0 : 0 < eta)
    (heta : eta ≤ lossMeanVariance E H q
      / (lossMeanVariance E H q + minimalWithinVariance E H q)) :
    lossMeanVariance E H q + minimalWithinVariance E H q
      ≤ lossMeanVariance E H q / eta := by
  have hsum : 0 < lossMeanVariance E H q + minimalWithinVariance E H q := by linarith
  have hmul : eta * (lossMeanVariance E H q + minimalWithinVariance E H q)
      ≤ lossMeanVariance E H q := (le_div_iff₀ hsum).mp heta
  rw [le_div_iff₀ heta0]
  nlinarith

/-- The shape parameter realizing a prescribed loss-explainability: TQ Theorem 8.1's
explicit inverse `p = τ²/(τ² + B/η − B − W₀)`. -/
def spikeParameter (E : ExpFunctional D) (H : ℝ) (q : D → ℝ) (eta : ℝ) : ℝ :=
  (1 - H) ^ 2 / ((1 - H) ^ 2 + lossMeanVariance E H q / eta
    - lossMeanVariance E H q - minimalWithinVariance E H q)

/-- The prescribed shape parameter is an admissible probability weight. -/
theorem spikeParameter_mem_unit (E : ExpFunctional D) (H : ℝ) (q : D → ℝ) (eta : ℝ)
    (hH1 : H < 1) (hW : 0 ≤ minimalWithinVariance E H q)
    (hB : 0 < lossMeanVariance E H q) (heta0 : 0 < eta)
    (heta : eta ≤ lossMeanVariance E H q
      / (lossMeanVariance E H q + minimalWithinVariance E H q)) :
    0 < spikeParameter E H q eta ∧ spikeParameter E H q eta ≤ 1 := by
  have htau : 0 < (1 - H) ^ 2 := pow_pos (by linarith) 2
  have hslack := lossBudget_slack E H q eta hW hB heta0 heta
  have hden : 0 < (1 - H) ^ 2 + lossMeanVariance E H q / eta
      - lossMeanVariance E H q - minimalWithinVariance E H q := by linarith
  unfold spikeParameter
  exact ⟨div_pos htau hden, (div_le_one hden).mpr (by linarith)⟩

/-- **Every value in `(0, B/(B+W₀)]` is attained by the explicit noise family.** -/
theorem spike_realizes_fraction (E : ExpFunctional D) (H : ℝ) (q : D → ℝ) (eta : ℝ)
    (hH : 0 ≤ H) (hH1 : H < 1) (hq0 : ∀ d, 0 ≤ q d) (hqH : ∀ d, q d ≤ H)
    (hB : 0 < lossMeanVariance E H q) (heta0 : 0 < eta)
    (heta : eta ≤ lossMeanVariance E H q
      / (lossMeanVariance E H q + minimalWithinVariance E H q))
    (hp : 0 < spikeParameter E H q eta) (hp1 : spikeParameter E H q eta ≤ 1) :
    lossExplainedFraction E (spikeLaw (spikeParameter E H q eta) hp hp1) H q
        (spikeValue H (spikeParameter E H q eta)) = eta := by
  have hW : 0 ≤ minimalWithinVariance E H q := minimalWithinVariance_nonneg E H q hH1.le
  have htau : 0 < (1 - H) ^ 2 := pow_pos (by linarith) 2
  have hslack := lossBudget_slack E H q eta hW hB heta0 heta
  have hden : 0 < (1 - H) ^ 2 + lossMeanVariance E H q / eta
      - lossMeanVariance E H q - minimalWithinVariance E H q := by linarith
  have hinv : (spikeParameter E H q eta)⁻¹
      = ((1 - H) ^ 2 + lossMeanVariance E H q / eta
          - lossMeanVariance E H q - minimalWithinVariance E H q) / (1 - H) ^ 2 := by
    unfold spikeParameter
    rw [inv_div]
  have hHne : (1:ℝ) - H ≠ 0 := ne_of_gt (by linarith)
  have hetane : eta ≠ 0 := ne_of_gt heta0
  have hBne : lossMeanVariance E H q ≠ 0 := ne_of_gt hB
  have hcancel : (1 - H) ^ 2 * (((1 - H) ^ 2 + lossMeanVariance E H q / eta
          - lossMeanVariance E H q - minimalWithinVariance E H q) / (1 - H) ^ 2)
      = (1 - H) ^ 2 + lossMeanVariance E H q / eta
          - lossMeanVariance E H q - minimalWithinVariance E H q := by
    field_simp <;> ring
  have hdenom : lossMeanVariance E H q + minimalWithinVariance E H q
      + (1 - H) ^ 2 * (((1 - H) ^ 2 + lossMeanVariance E H q / eta
          - lossMeanVariance E H q - minimalWithinVariance E H q) / (1 - H) ^ 2 - 1)
      = lossMeanVariance E H q / eta := by
    rw [mul_sub, hcancel, mul_one]
    ring
  rw [spike_loss_fraction E H q _ hp hp1 hH hH1.le hq0 hqH, hinv, hdenom]
  field_simp <;> ring

/-- **TQ Theorem 8.1, equation (8.3): the attainable set of the distance-explained
fraction of individual squared loss is exactly `(0, B/(B+W₀)]`**, on one fixed genotype
law, one fixed heritability and one fixed prescribed curve, varying only the shape of
the environmental noise. -/
theorem sharp_loss_fraction_interval (E : ExpFunctional D) (H : ℝ) (q : D → ℝ)
    (eta : ℝ) (hH : 0 ≤ H) (hH1 : H < 1) (hq0 : ∀ d, 0 ≤ q d) (hqH : ∀ d, q d ≤ H)
    (hB : 0 < lossMeanVariance E H q) :
    (∃ (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1),
        lossExplainedFraction E (spikeLaw p hp hp1) H q (spikeValue H p) = eta)
      ↔ 0 < eta ∧ eta ≤ lossMeanVariance E H q
          / (lossMeanVariance E H q + minimalWithinVariance E H q) := by
  constructor
  · rintro ⟨p, hp, hp1, rfl⟩
    exact loss_fraction_bounds E (spikeLaw p hp hp1) H q (spikeValue H p) hH hH1.le hq0
      hqH (spike_second_moment H p hp hp1 hH1.le) hB
  · rintro ⟨heta0, heta⟩
    obtain ⟨hp, hp1⟩ := spikeParameter_mem_unit E H q eta hH1
      (minimalWithinVariance_nonneg E H q hH1.le) hB heta0 heta
    exact ⟨spikeParameter E H q eta, hp, hp1,
      spike_realizes_fraction E H q eta hH hH1 hq0 hqH hB heta0 heta hp hp1⟩

/-- **TQ Theorem 8.1 in full: every admissible loss-explainability coexists with the
originally prescribed cellwise squared-correlation curve and the same cellwise
heritability.**  The genotype law, the deployed source-trained score, the cellwise
outcome variance, the cellwise genotype-explained fraction and the cellwise curve are
all fixed; only the environmental noise shape moves. -/
theorem simultaneous_curve_and_loss_fraction (E : ExpFunctional D) (H : ℝ) (q : D → ℝ)
    (eta : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (hq0 : ∀ d, 0 ≤ q d) (hqH : ∀ d, q d ≤ H)
    (hB : 0 < lossMeanVariance E H q) (heta0 : 0 < eta)
    (heta : eta ≤ lossMeanVariance E H q
      / (lossMeanVariance E H q + minimalWithinVariance E H q)) :
    ∃ (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1),
      lossExplainedFraction E (spikeLaw p hp hp1) H q (spikeValue H p) = eta ∧
        ∀ d : D,
          variance (cellLaw (spikeLaw p hp hp1))
              (cellPhenotype H q (spikeValue H p) d) = 1 ∧
            genotypeExplainedFraction (uniformExp (Bool × Bool))
                (fun _ ↦ spikeLaw p hp hp1) (cellPhenotype H q (spikeValue H p) d) = H ∧
              scoreAccuracy (uniformExp (Bool × Bool)) (fun _ ↦ spikeLaw p hp hp1)
                (deployedScore H) (cellPhenotype H q (spikeValue H p) d) = q d := by
  obtain ⟨hp, hp1⟩ := spikeParameter_mem_unit E H q eta hH1
    (minimalWithinVariance_nonneg E H q hH1.le) hB heta0 heta
  refine ⟨spikeParameter E H q eta, hp, hp1,
    spike_realizes_fraction E H q eta hH0.le hH1 hq0 hqH hB heta0 heta hp hp1, fun d ↦ ?_⟩
  exact fixed_background_curve_realized (spikeLaw (spikeParameter E H q eta) hp hp1) H q
    (spikeValue H (spikeParameter E H q eta)) d hH0 (hq0 d) (hqH d)
    (spike_mean H _ hp hp1) (spike_second_moment H _ hp hp1 hH1.le)

/-! ### The four-cell worked example of TQ §8.2 -/

/-- The nonmonotone curve `q = (0.36, 0.16, 0.04, 0.25)` of TQ §8.2, at heritability
`H = 2/5`. -/
def workedCurve : Fin 4 → ℝ := ![9 / 25, 4 / 25, 1 / 25, 1 / 4]

/-- The worked curve is nonnegative. -/
theorem workedCurve_nonneg (d : Fin 4) : 0 ≤ workedCurve d := by
  fin_cases d
  · show (0:ℝ) ≤ 9 / 25
    norm_num
  · show (0:ℝ) ≤ 4 / 25
    norm_num
  · show (0:ℝ) ≤ 1 / 25
    norm_num
  · show (0:ℝ) ≤ 1 / 4
    norm_num

/-- The worked curve stays below the heritability. -/
theorem workedCurve_le (d : Fin 4) : workedCurve d ≤ 2 / 5 := by
  fin_cases d
  · show (9:ℝ) / 25 ≤ 2 / 5
    norm_num
  · show (4:ℝ) / 25 ≤ 2 / 5
    norm_num
  · show (1:ℝ) / 25 ≤ 2 / 5
    norm_num
  · show (1:ℝ) / 4 ≤ 2 / 5
    norm_num

/-- Mean individual loss in the first cell of the worked example. -/
theorem lossMean_worked_zero :
    lossMean (2 / 5) workedCurve 0 = 7 / 5 - 6 / 5 * Real.sqrt (2 / 5) := by
  have h : Real.sqrt (workedCurve 0) = 3 / 5 := by
    show Real.sqrt (9 / 25) = 3 / 5
    rw [show (9:ℝ) / 25 = (3 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  unfold lossMean
  rw [h]
  ring

/-- Mean individual loss in the second cell of the worked example. -/
theorem lossMean_worked_one :
    lossMean (2 / 5) workedCurve 1 = 7 / 5 - 4 / 5 * Real.sqrt (2 / 5) := by
  have h : Real.sqrt (workedCurve 1) = 2 / 5 := by
    show Real.sqrt (4 / 25) = 2 / 5
    rw [show (4:ℝ) / 25 = (2 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  unfold lossMean
  rw [h]
  ring

/-- Mean individual loss in the third cell of the worked example. -/
theorem lossMean_worked_two :
    lossMean (2 / 5) workedCurve 2 = 7 / 5 - 2 / 5 * Real.sqrt (2 / 5) := by
  have h : Real.sqrt (workedCurve 2) = 1 / 5 := by
    show Real.sqrt (1 / 25) = 1 / 5
    rw [show (1:ℝ) / 25 = (1 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  unfold lossMean
  rw [h]
  ring

/-- Mean individual loss in the fourth cell of the worked example. -/
theorem lossMean_worked_three :
    lossMean (2 / 5) workedCurve 3 = 7 / 5 - Real.sqrt (2 / 5) := by
  have h : Real.sqrt (workedCurve 3) = 1 / 2 := by
    show Real.sqrt (1 / 4) = 1 / 2
    rw [show (1:ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  unfold lossMean
  rw [h]
  ring

/-- **The between-cell loss variance of the worked example is exactly `7/200`.**  The
irrational `√H` cancels: `B = 4H · Var(√q)`. -/
theorem worked_lossMeanVariance :
    lossMeanVariance (uniformExp (Fin 4)) (2 / 5) workedCurve = 7 / 200 := by
  have hr : Real.sqrt (2 / 5) ^ 2 = 2 / 5 := Real.sq_sqrt (by norm_num)
  unfold lossMeanVariance
  rw [variance_eq_expect_sq_sub_sq_mean]
  simp only [uniformExp_apply, Fintype.card_fin, Fin.sum_univ_four]
  rw [lossMean_worked_zero, lossMean_worked_one, lossMean_worked_two,
    lossMean_worked_three]
  linear_combination (35 / 400 : ℝ) * hr

/-- **The hypothesis `B > 0` of TQ Theorem 8.1 is satisfiable**, so the theorem is not
vacuous: the manuscript's own four-cell example supplies a positive value. -/
theorem worked_example_positive_variance :
    0 < lossMeanVariance (uniformExp (Fin 4)) (2 / 5) workedCurve := by
  rw [worked_lossMeanVariance]
  norm_num

/-- **TQ §8.2: the sharp interval at the manuscript's own four-cell example**, with the
between-cell variance evaluated exactly. -/
theorem worked_example_sharp_interval (eta : ℝ) :
    (∃ (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1),
        lossExplainedFraction (uniformExp (Fin 4)) (spikeLaw p hp hp1) (2 / 5)
          workedCurve (spikeValue (2 / 5) p) = eta)
      ↔ 0 < eta ∧ eta ≤ 7 / 200
          / (7 / 200 + minimalWithinVariance (uniformExp (Fin 4)) (2 / 5) workedCurve) := by
  have h := sharp_loss_fraction_interval (uniformExp (Fin 4)) (2 / 5) workedCurve eta
    (by norm_num) (by norm_num) workedCurve_nonneg workedCurve_le
    worked_example_positive_variance
  rw [worked_lossMeanVariance] at h
  exact h

end

end Descent.Portability.SimultaneousRealization
