/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IndividualLossMoments

assert_below Descent.Decision Descent.Program

/-!
# Sharp additive-noise completion of the conditional squared-loss variance

TQ Theorem 2.5. The genetic part `g` of the residual and the conditional noise
variance `τ` are held fixed; only the shape of the conditional noise law varies.
In a distance cell the joint conditional law is `mixture KG (fun _ ↦ KN)`, the
product of the genetic law with the noise law, which is exactly the manuscript's
"conditional on distance, the noise is independent of genotype". The exact
conditional loss variance (2.12), its completed-square form (2.9), the
third/fourth-moment inequality (2.13) and the sharp lower bound (2.10) are
proved, and for every prescribed excess `δ ≥ 0` an explicit two-point noise law
`zeroMeanNoise` attaining `minCellLossVariance + δ` is exhibited with its four
exact moments (2.11). The only hypotheses are the manuscript's domain
conditions: a positive noise variance in the cell and a nonnegative excess.
This builds on `mixture` and `total_variance` of `IndividualLossMoments` and on
`variance`, `ExpFunctional` and `weightedExp` of the foundations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.LossNoiseCompletion

open Foundations IndividualLossMoments

noncomputable section

variable {G N : Type*}

/-- The mean-zero two-point law on `Bool` supported on `{-α, β}` with `α, β > 0`.
The mass at `β` is `α / (α + β)` and the mass at `-α` is `β / (α + β)`, so the
mean is zero. Every finite-support mean-zero law with two atoms has this form. -/
def twoPointLaw (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) : ExpFunctional Bool :=
  weightedExp (fun b ↦ cond b (α / (α + β)) (β / (α + β)))
    (by
      intro b
      cases b
      · exact div_nonneg hβ.le (by linarith)
      · exact div_nonneg hα.le (by linarith))
    (by
      rw [Fintype.sum_bool]
      show α / (α + β) + β / (α + β) = 1
      rw [← add_div, div_self (ne_of_gt (by linarith : (0 : ℝ) < α + β))])

/-- The support values of `twoPointLaw`: `β` at `true` and `-α` at `false`. -/
def twoPointValue (α β : ℝ) : Bool → ℝ := fun b ↦ cond b β (-α)

/-- Evaluation of the two-point law against an arbitrary observable. -/
theorem twoPointLaw_apply (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (f : Bool → ℝ) :
    twoPointLaw α β hα hβ f = (α * f true + β * f false) / (α + β) := by
  simp only [twoPointLaw, weightedExp_apply, Fintype.sum_bool]
  show α / (α + β) * f true + β / (α + β) * f false
      = (α * f true + β * f false) / (α + β)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]

/-- The two-point law has mean zero. -/
theorem twoPointLaw_mean (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    twoPointLaw α β hα hβ (twoPointValue α β) = 0 := by
  rw [twoPointLaw_apply]
  show (α * β + β * -α) / (α + β) = 0
  rw [div_eq_zero_iff]
  left
  ring

/-- Its second moment is the product of the two support magnitudes. -/
theorem twoPointLaw_second (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    twoPointLaw α β hα hβ (fun b ↦ twoPointValue α β b ^ 2) = α * β := by
  have hs : α + β ≠ 0 := ne_of_gt (by linarith)
  rw [twoPointLaw_apply]
  show (α * β ^ 2 + β * (-α) ^ 2) / (α + β) = α * β
  rw [div_eq_iff hs]
  ring

/-- Its third moment is `αβ(β - α)`: the skewness is carried by the asymmetry. -/
theorem twoPointLaw_third (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    twoPointLaw α β hα hβ (fun b ↦ twoPointValue α β b ^ 3) = α * β * (β - α) := by
  have hs : α + β ≠ 0 := ne_of_gt (by linarith)
  rw [twoPointLaw_apply]
  show (α * β ^ 3 + β * (-α) ^ 3) / (α + β) = α * β * (β - α)
  rw [div_eq_iff hs]
  ring

/-- Its fourth moment is `αβ((β - α)² + αβ)`. -/
theorem twoPointLaw_fourth (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    twoPointLaw α β hα hβ (fun b ↦ twoPointValue α β b ^ 4)
      = α * β * ((β - α) ^ 2 + α * β) := by
  have hs : α + β ≠ 0 := ne_of_gt (by linarith)
  rw [twoPointLaw_apply]
  show (α * β ^ 4 + β * (-α) ^ 4) / (α + β) = α * β * ((β - α) ^ 2 + α * β)
  rw [div_eq_iff hs]
  ring

/-- The negative support magnitude of the mean-zero law with variance `v` and
skewness parameter `h`: the smaller root of `x² - hx - v`, in absolute value. -/
def gapRoot (v h : ℝ) : ℝ := (Real.sqrt (h ^ 2 + 4 * v) - h) / 2

/-- Both support magnitudes are positive whenever the prescribed variance is. -/
theorem gapRoot_bounds (v h : ℝ) (hv : 0 < v) :
    0 < gapRoot v h ∧ 0 < gapRoot v h + h := by
  have habs : |h| < Real.sqrt (h ^ 2 + 4 * v) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg h) (by linarith)
  obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
  constructor
  · unfold gapRoot
    linarith
  · unfold gapRoot
    linarith

/-- The two support magnitudes multiply to the prescribed variance. -/
theorem gapRoot_mul (v h : ℝ) (hv : 0 ≤ v) :
    gapRoot v h * (gapRoot v h + h) = v := by
  have hs2 : Real.sqrt (h ^ 2 + 4 * v) ^ 2 = h ^ 2 + 4 * v :=
    Real.sq_sqrt (by positivity)
  unfold gapRoot
  linear_combination hs2 / 4

/-- The mean-zero two-point noise law with conditional variance `v` and
skewness parameter `h`: its third moment is `hv` and its fourth is `v² + h²v`.
This is the noise family of TQ (2.14). -/
def zeroMeanNoise (v h : ℝ) (hv : 0 < v) : ExpFunctional Bool :=
  twoPointLaw (gapRoot v h) (gapRoot v h + h) (gapRoot_bounds v h hv).1
    (gapRoot_bounds v h hv).2

/-- The support values of `zeroMeanNoise`. -/
def zeroMeanNoiseValue (v h : ℝ) : Bool → ℝ :=
  twoPointValue (gapRoot v h) (gapRoot v h + h)

/-- The completion noise has mean zero. -/
theorem zeroMeanNoise_mean (v h : ℝ) (hv : 0 < v) :
    zeroMeanNoise v h hv (zeroMeanNoiseValue v h) = 0 :=
  twoPointLaw_mean _ _ _ _

/-- Its second moment is exactly the prescribed conditional variance. -/
theorem zeroMeanNoise_second (v h : ℝ) (hv : 0 < v) :
    zeroMeanNoise v h hv (fun b ↦ zeroMeanNoiseValue v h b ^ 2) = v := by
  simp only [zeroMeanNoise, zeroMeanNoiseValue]
  rw [twoPointLaw_second, gapRoot_mul v h hv.le]

/-- Its third moment is `h * v`, so `h` is the free skewness parameter. -/
theorem zeroMeanNoise_third (v h : ℝ) (hv : 0 < v) :
    zeroMeanNoise v h hv (fun b ↦ zeroMeanNoiseValue v h b ^ 3) = h * v := by
  simp only [zeroMeanNoise, zeroMeanNoiseValue]
  rw [twoPointLaw_third, gapRoot_mul v h hv.le]
  ring

/-- Its fourth moment is `v² + h²v`, the equality case of TQ (2.13). -/
theorem zeroMeanNoise_fourth (v h : ℝ) (hv : 0 < v) :
    zeroMeanNoise v h hv (fun b ↦ zeroMeanNoiseValue v h b ^ 4) = v ^ 2 + h ^ 2 * v := by
  simp only [zeroMeanNoise, zeroMeanNoiseValue]
  rw [twoPointLaw_fourth, gapRoot_mul v h hv.le]
  ring

/-- Shifting a mean-zero law by a constant: the second moment. -/
theorem noise_shift_second_moment (KN : ExpFunctional N) (e : N → ℝ)
    (hmean : KN e = 0) (c : ℝ) :
    KN (fun n ↦ (c + e n) ^ 2) = c ^ 2 + KN (fun n ↦ e n ^ 2) := by
  have hsplit : (fun n ↦ (c + e n) ^ 2)
      = (fun n ↦ e n ^ 2) + (2 * c) • e + (fun _ : N ↦ c ^ 2) := by
    funext n
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit, KN.add_eval, KN.add_eval, KN.smul_eval, KN.eval_const, hmean]
  ring

/-- Shifting a mean-zero law by a constant: the fourth moment, which is where
the noise skewness `t₃` and kurtosis `t₄` enter the loss variance. -/
theorem noise_shift_fourth_moment (KN : ExpFunctional N) (e : N → ℝ)
    (hmean : KN e = 0) (c : ℝ) :
    KN (fun n ↦ (c + e n) ^ 4)
      = c ^ 4 + 6 * c ^ 2 * KN (fun n ↦ e n ^ 2) + 4 * c * KN (fun n ↦ e n ^ 3)
        + KN (fun n ↦ e n ^ 4) := by
  have hsplit : (fun n ↦ (c + e n) ^ 4)
      = (fun n ↦ e n ^ 4) + (4 * c) • (fun n ↦ e n ^ 3)
        + (6 * c ^ 2) • (fun n ↦ e n ^ 2) + (4 * c ^ 3) • e
        + (fun _ : N ↦ c ^ 4) := by
    funext n
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit, KN.add_eval, KN.add_eval, KN.add_eval, KN.add_eval, KN.smul_eval,
    KN.smul_eval, KN.smul_eval, KN.eval_const, hmean]
  ring

/-- TQ (2.8): the conditional mean loss in a cell is the genetic second moment
plus the noise variance, independently of the noise shape. -/
theorem additive_noise_cell_mean_loss (KG : ExpFunctional G) (KN : ExpFunctional N)
    (g : G → ℝ) (e : N → ℝ) (hmean : KN e = 0) :
    mixture KG (fun _ ↦ KN) (fun z ↦ (g z.1 + e z.2) ^ 2)
      = KG (fun γ ↦ g γ ^ 2) + KN (fun n ↦ e n ^ 2) := by
  show KG (fun γ ↦ KN (fun n ↦ (g γ + e n) ^ 2)) = _
  simp only [noise_shift_second_moment KN e hmean]
  rw [show (fun γ ↦ g γ ^ 2 + KN (fun n ↦ e n ^ 2))
      = (fun γ ↦ g γ ^ 2) + (fun _ : G ↦ KN (fun n ↦ e n ^ 2)) from rfl,
    KG.add_eval, KG.eval_const]

/-- The conditional fourth moment of the residual in a cell. -/
theorem additive_noise_cell_fourth_moment (KG : ExpFunctional G)
    (KN : ExpFunctional N) (g : G → ℝ) (e : N → ℝ) (hmean : KN e = 0) :
    mixture KG (fun _ ↦ KN) (fun z ↦ (g z.1 + e z.2) ^ 4)
      = KG (fun γ ↦ g γ ^ 4) + 6 * KG (fun γ ↦ g γ ^ 2) * KN (fun n ↦ e n ^ 2)
        + 4 * KG g * KN (fun n ↦ e n ^ 3) + KN (fun n ↦ e n ^ 4) := by
  show KG (fun γ ↦ KN (fun n ↦ (g γ + e n) ^ 4)) = _
  simp only [noise_shift_fourth_moment KN e hmean]
  have hsplit : (fun γ ↦ g γ ^ 4 + 6 * g γ ^ 2 * KN (fun n ↦ e n ^ 2)
        + 4 * g γ * KN (fun n ↦ e n ^ 3) + KN (fun n ↦ e n ^ 4))
      = (fun γ ↦ g γ ^ 4) + (6 * KN (fun n ↦ e n ^ 2)) • (fun γ ↦ g γ ^ 2)
        + (4 * KN (fun n ↦ e n ^ 3)) • g + (fun _ : G ↦ KN (fun n ↦ e n ^ 4)) := by
    funext γ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit, KG.add_eval, KG.add_eval, KG.add_eval, KG.smul_eval, KG.smul_eval,
    KG.eval_const]
  ring

/-- TQ (2.12): the exact conditional variance of squared error under additive
noise that is conditionally independent of genotype. `a`, `r`, `J` are the
genetic first, second and fourth moments; `τ`, `t₃`, `t₄` the noise moments. -/
theorem additive_noise_cell_loss_variance (KG : ExpFunctional G)
    (KN : ExpFunctional N) (g : G → ℝ) (e : N → ℝ) (a r J τ t₃ t₄ : ℝ)
    (hmean : KN e = 0) (ha : KG g = a) (hr : KG (fun γ ↦ g γ ^ 2) = r)
    (hJ : KG (fun γ ↦ g γ ^ 4) = J) (hτ : KN (fun n ↦ e n ^ 2) = τ)
    (h₃ : KN (fun n ↦ e n ^ 3) = t₃) (h₄ : KN (fun n ↦ e n ^ 4) = t₄) :
    variance (mixture KG (fun _ ↦ KN)) (fun z ↦ (g z.1 + e z.2) ^ 2)
      = J - r ^ 2 + 4 * τ * r + 4 * a * t₃ + t₄ - τ ^ 2 := by
  simp only [variance_eq_expect_sq_sub_sq_mean, ← pow_mul]
  rw [additive_noise_cell_fourth_moment KG KN g e hmean,
    additive_noise_cell_mean_loss KG KN g e hmean, ha, hr, hJ, hτ, h₃, h₄]
  ring

/-- TQ (2.13): projecting `ε²` on the span of `1` and `ε` shows the residual
kurtosis term is nonnegative, with equality exactly for two-point noise. -/
theorem noise_fourth_moment_projection_nonneg (KN : ExpFunctional N) (e : N → ℝ)
    (τ t₃ t₄ : ℝ) (hmean : KN e = 0) (hτ : KN (fun n ↦ e n ^ 2) = τ)
    (h₃ : KN (fun n ↦ e n ^ 3) = t₃) (h₄ : KN (fun n ↦ e n ^ 4) = t₄)
    (hτpos : 0 < τ) : 0 ≤ t₄ - τ ^ 2 - t₃ ^ 2 / τ := by
  have hne : τ ≠ 0 := ne_of_gt hτpos
  have hnn : 0 ≤ KN (fun n ↦ (e n ^ 2 - τ - t₃ / τ * e n) ^ 2) :=
    KN.nonneg_eval _ (fun n ↦ sq_nonneg _)
  have hsplit : (fun n ↦ (e n ^ 2 - τ - t₃ / τ * e n) ^ 2)
      = (fun n ↦ e n ^ 4) + (-(2 * (t₃ / τ))) • (fun n ↦ e n ^ 3)
        + ((t₃ / τ) ^ 2 - 2 * τ) • (fun n ↦ e n ^ 2) + (2 * τ * (t₃ / τ)) • e
        + (fun _ : N ↦ τ ^ 2) := by
    funext n
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hexp : KN (fun n ↦ (e n ^ 2 - τ - t₃ / τ * e n) ^ 2)
      = t₄ - τ ^ 2 - t₃ ^ 2 / τ := by
    rw [hsplit, KN.add_eval, KN.add_eval, KN.add_eval, KN.add_eval, KN.smul_eval,
      KN.smul_eval, KN.smul_eval, KN.eval_const, hmean, hτ, h₃, h₄]
    field_simp
    try ring
  linarith [hexp ▸ hnn]

/-- TQ (2.9): the completed-square form, exhibiting the minimum, the skewness
square and the nonnegative kurtosis remainder as separate terms. -/
theorem additive_noise_cell_loss_variance_square_form (KG : ExpFunctional G)
    (KN : ExpFunctional N) (g : G → ℝ) (e : N → ℝ) (a r J τ t₃ t₄ : ℝ)
    (hmean : KN e = 0) (ha : KG g = a) (hr : KG (fun γ ↦ g γ ^ 2) = r)
    (hJ : KG (fun γ ↦ g γ ^ 4) = J) (hτ : KN (fun n ↦ e n ^ 2) = τ)
    (h₃ : KN (fun n ↦ e n ^ 3) = t₃) (h₄ : KN (fun n ↦ e n ^ 4) = t₄)
    (hτpos : 0 < τ) :
    variance (mixture KG (fun _ ↦ KN)) (fun z ↦ (g z.1 + e z.2) ^ 2)
      = J - r ^ 2 + 4 * τ * (r - a ^ 2) + (t₃ + 2 * a * τ) ^ 2 / τ
        + (t₄ - τ ^ 2 - t₃ ^ 2 / τ) := by
  have hne : τ ≠ 0 := ne_of_gt hτpos
  rw [additive_noise_cell_loss_variance KG KN g e a r J τ t₃ t₄ hmean ha hr hJ hτ
    h₃ h₄]
  field_simp
  try ring

/-- The minimal conditional loss variance `W_min` of TQ Theorem 2.5: the value
forced by the genetic part and the noise variance alone. -/
def minCellLossVariance (KG : ExpFunctional G) (g : G → ℝ) (τ : ℝ) : ℝ :=
  variance KG (fun γ ↦ g γ ^ 2) + 4 * τ * variance KG g

/-- `W_min` in raw genetic moments, as displayed in TQ (2.9). -/
theorem minCellLossVariance_eq_raw_moments (KG : ExpFunctional G) (g : G → ℝ)
    (a r J τ : ℝ) (ha : KG g = a) (hr : KG (fun γ ↦ g γ ^ 2) = r)
    (hJ : KG (fun γ ↦ g γ ^ 4) = J) :
    minCellLossVariance KG g τ = J - r ^ 2 + 4 * τ * (r - a ^ 2) := by
  unfold minCellLossVariance
  simp only [variance_eq_expect_sq_sub_sq_mean, ← pow_mul]
  rw [ha, hr, hJ]

/-- `W_min` is nonnegative, so the fixed-architecture denominator cannot shrink
below the between-cell term. -/
theorem minCellLossVariance_nonneg (KG : ExpFunctional G) (g : G → ℝ) (τ : ℝ)
    (hτ : 0 ≤ τ) : 0 ≤ minCellLossVariance KG g τ := by
  have h1 : 0 ≤ variance KG (fun γ ↦ g γ ^ 2) :=
    KG.nonneg_eval _ (fun _ ↦ sq_nonneg _)
  have h2 : 0 ≤ variance KG g := KG.nonneg_eval _ (fun _ ↦ sq_nonneg _)
  unfold minCellLossVariance
  nlinarith

/-- TQ (2.10): the sharp lower bound on the conditional loss variance, valid for
every admissible conditional noise shape with the prescribed variance. -/
theorem additive_noise_cell_loss_variance_lower_bound (KG : ExpFunctional G)
    (KN : ExpFunctional N) (g : G → ℝ) (e : N → ℝ) (τ : ℝ) (hmean : KN e = 0)
    (hτ : KN (fun n ↦ e n ^ 2) = τ) (hτpos : 0 < τ) :
    minCellLossVariance KG g τ
      ≤ variance (mixture KG (fun _ ↦ KN)) (fun z ↦ (g z.1 + e z.2) ^ 2) := by
  rw [minCellLossVariance_eq_raw_moments KG g (KG g) (KG (fun γ ↦ g γ ^ 2))
    (KG (fun γ ↦ g γ ^ 4)) τ rfl rfl rfl,
    additive_noise_cell_loss_variance_square_form KG KN g e (KG g)
      (KG (fun γ ↦ g γ ^ 2)) (KG (fun γ ↦ g γ ^ 4)) τ (KN (fun n ↦ e n ^ 3))
      (KN (fun n ↦ e n ^ 4)) hmean rfl rfl rfl hτ rfl rfl hτpos]
  have h1 : 0 ≤ (KN (fun n ↦ e n ^ 3) + 2 * KG g * τ) ^ 2 / τ :=
    div_nonneg (sq_nonneg _) hτpos.le
  have h2 := noise_fourth_moment_projection_nonneg KN e τ (KN (fun n ↦ e n ^ 3))
    (KN (fun n ↦ e n ^ 4)) hmean hτ rfl rfl hτpos
  linarith

/-- The exact conditional loss variance of the two-point completion: the
minimum plus `τ(h + 2a)²`, where `h` is the free skewness parameter. -/
theorem zeroMeanNoise_cell_loss_variance_general (KG : ExpFunctional G)
    (g : G → ℝ) (τ hpar : ℝ) (hτ : 0 < τ) :
    variance (mixture KG (fun _ ↦ zeroMeanNoise τ hpar hτ))
        (fun z ↦ (g z.1 + zeroMeanNoiseValue τ hpar z.2) ^ 2)
      = minCellLossVariance KG g τ + τ * (hpar + 2 * KG g) ^ 2 := by
  rw [additive_noise_cell_loss_variance KG (zeroMeanNoise τ hpar hτ) g
      (zeroMeanNoiseValue τ hpar) (KG g) (KG (fun γ ↦ g γ ^ 2))
      (KG (fun γ ↦ g γ ^ 4)) τ (hpar * τ) (τ ^ 2 + hpar ^ 2 * τ)
      (zeroMeanNoise_mean τ hpar hτ) rfl rfl rfl (zeroMeanNoise_second τ hpar hτ)
      (zeroMeanNoise_third τ hpar hτ) (zeroMeanNoise_fourth τ hpar hτ),
    minCellLossVariance_eq_raw_moments KG g (KG g) (KG (fun γ ↦ g γ ^ 2))
      (KG (fun γ ↦ g γ ^ 4)) τ rfl rfl rfl]
  ring

/-- TQ (2.11): for every prescribed finite excess `δ ≥ 0` there is a conditional
two-point noise law, independent of genotype given distance and with the same
zero mean and variance `τ`, whose conditional loss variance is exactly
`W_min + δ`. Taking `δ = 0` shows the bound (2.10) is attained. -/
theorem zeroMeanNoise_cell_loss_variance (KG : ExpFunctional G) (g : G → ℝ)
    (τ δ : ℝ) (hτ : 0 < τ) (hδ : 0 ≤ δ) :
    variance (mixture KG (fun _ ↦ zeroMeanNoise τ (-2 * KG g + Real.sqrt (δ / τ)) hτ))
        (fun z ↦ (g z.1
          + zeroMeanNoiseValue τ (-2 * KG g + Real.sqrt (δ / τ)) z.2) ^ 2)
      = minCellLossVariance KG g τ + δ := by
  have hne : τ ≠ 0 := ne_of_gt hτ
  rw [zeroMeanNoise_cell_loss_variance_general KG g τ
    (-2 * KG g + Real.sqrt (δ / τ)) hτ]
  have hshift : -2 * KG g + Real.sqrt (δ / τ) + 2 * KG g = Real.sqrt (δ / τ) := by
    ring
  rw [hshift, Real.sq_sqrt (div_nonneg hδ hτ.le)]
  field_simp

variable {D : Type*}

/-- Total loss variance in the fixed-architecture setting of TQ §2.4: the
between-cell variance of the conditional mean loss `r + τ` plus the mean
conditional loss variance. `W` names the cell loss variance function. -/
theorem fixed_architecture_total_loss_variance (E : ExpFunctional D)
    (KG : D → ExpFunctional G) (KN : D → ExpFunctional N) (g : D × G → ℝ)
    (e : D × N → ℝ) (τ W : D → ℝ)
    (hmean : ∀ d, KN d (fun n ↦ e (d, n)) = 0)
    (hτ : ∀ d, KN d (fun n ↦ e (d, n) ^ 2) = τ d)
    (hW : ∀ d, variance (mixture (KG d) (fun _ ↦ KN d))
      (fun z ↦ (g (d, z.1) + e (d, z.2)) ^ 2) = W d) :
    variance (mixture E (fun d ↦ mixture (KG d) (fun _ ↦ KN d)))
        (fun z ↦ (g (z.1, z.2.1) + e (z.1, z.2.2)) ^ 2)
      = variance E (fun d ↦ KG d (fun γ ↦ g (d, γ) ^ 2) + τ d) + E W := by
  have ht := total_variance E (fun d ↦ mixture (KG d) (fun _ ↦ KN d))
    (fun z : D × (G × N) ↦ (g (z.1, z.2.1) + e (z.1, z.2.2)) ^ 2)
  have hfun1 : (fun d ↦ variance (mixture (KG d) (fun _ ↦ KN d))
      (fun ω : G × N ↦ (g (d, ω.1) + e (d, ω.2)) ^ 2)) = W := by
    funext d
    exact hW d
  have hfun2 : (fun d ↦ mixture (KG d) (fun _ ↦ KN d)
      (fun ω : G × N ↦ (g (d, ω.1) + e (d, ω.2)) ^ 2))
      = (fun d ↦ KG d (fun γ ↦ g (d, γ) ^ 2) + τ d) := by
    funext d
    have hc := additive_noise_cell_mean_loss (KG d) (KN d) (fun γ ↦ g (d, γ))
      (fun n ↦ e (d, n)) (hmean d)
    calc mixture (KG d) (fun _ ↦ KN d)
          (fun ω : G × N ↦ (g (d, ω.1) + e (d, ω.2)) ^ 2)
        = KG d (fun γ ↦ g (d, γ) ^ 2) + KN d (fun n ↦ e (d, n) ^ 2) := hc
      _ = KG d (fun γ ↦ g (d, γ) ^ 2) + τ d := by rw [hτ d]
  rw [ht]
  show E (fun d ↦ variance (mixture (KG d) (fun _ ↦ KN d))
      (fun ω : G × N ↦ (g (d, ω.1) + e (d, ω.2)) ^ 2))
      + variance E (fun d ↦ mixture (KG d) (fun _ ↦ KN d)
        (fun ω : G × N ↦ (g (d, ω.1) + e (d, ω.2)) ^ 2))
      = variance E (fun d ↦ KG d (fun γ ↦ g (d, γ) ^ 2) + τ d) + E W
  rw [hfun1, hfun2]
  ring

/-- The fixed-architecture denominator is at least `B + W₀` for every admissible
conditional noise shape: TQ (2.10) integrated over the cells. -/
theorem fixed_architecture_total_variance_lower_bound (E : ExpFunctional D)
    (KG : D → ExpFunctional G) (KN : D → ExpFunctional N) (g : D × G → ℝ)
    (e : D × N → ℝ) (τ : D → ℝ)
    (hmean : ∀ d, KN d (fun n ↦ e (d, n)) = 0)
    (hτ : ∀ d, KN d (fun n ↦ e (d, n) ^ 2) = τ d) (hτpos : ∀ d, 0 < τ d) :
    variance E (fun d ↦ KG d (fun γ ↦ g (d, γ) ^ 2) + τ d)
        + E (fun d ↦ minCellLossVariance (KG d) (fun γ ↦ g (d, γ)) (τ d))
      ≤ variance (mixture E (fun d ↦ mixture (KG d) (fun _ ↦ KN d)))
          (fun z ↦ (g (z.1, z.2.1) + e (z.1, z.2.2)) ^ 2) := by
  rw [fixed_architecture_total_loss_variance E KG KN g e τ
    (fun d ↦ variance (mixture (KG d) (fun _ ↦ KN d))
      (fun z ↦ (g (d, z.1) + e (d, z.2)) ^ 2)) hmean hτ (fun d ↦ rfl)]
  have hmono : E (fun d ↦ minCellLossVariance (KG d) (fun γ ↦ g (d, γ)) (τ d))
      ≤ E (fun d ↦ variance (mixture (KG d) (fun _ ↦ KN d))
        (fun z ↦ (g (d, z.1) + e (d, z.2)) ^ 2)) :=
    E.eval_mono (fun d ↦ additive_noise_cell_loss_variance_lower_bound (KG d)
      (KN d) (fun γ ↦ g (d, γ)) (fun n ↦ e (d, n)) (τ d) (hmean d) (hτ d)
      (hτpos d))
  linarith

/-- TQ (2.17): every admissible noise shape has a strictly positive explainable
fraction, and none exceeds `B / (B + W₀)`. Zero is an infimum, not attained. -/
theorem fixed_architecture_fraction_bounds (E : ExpFunctional D)
    (KG : D → ExpFunctional G) (KN : D → ExpFunctional N) (g : D × G → ℝ)
    (e : D × N → ℝ) (τ : D → ℝ)
    (hmean : ∀ d, KN d (fun n ↦ e (d, n)) = 0)
    (hτ : ∀ d, KN d (fun n ↦ e (d, n) ^ 2) = τ d) (hτpos : ∀ d, 0 < τ d)
    (hB : 0 < variance E (fun d ↦ KG d (fun γ ↦ g (d, γ) ^ 2) + τ d)) :
    0 < variance E (fun d ↦ KG d (fun γ ↦ g (d, γ) ^ 2) + τ d)
        / variance (mixture E (fun d ↦ mixture (KG d) (fun _ ↦ KN d)))
          (fun z ↦ (g (z.1, z.2.1) + e (z.1, z.2.2)) ^ 2) ∧
      variance E (fun d ↦ KG d (fun γ ↦ g (d, γ) ^ 2) + τ d)
          / variance (mixture E (fun d ↦ mixture (KG d) (fun _ ↦ KN d)))
            (fun z ↦ (g (z.1, z.2.1) + e (z.1, z.2.2)) ^ 2)
        ≤ variance E (fun d ↦ KG d (fun γ ↦ g (d, γ) ^ 2) + τ d)
          / (variance E (fun d ↦ KG d (fun γ ↦ g (d, γ) ^ 2) + τ d)
            + E (fun d ↦ minCellLossVariance (KG d) (fun γ ↦ g (d, γ)) (τ d))) := by
  have hW0 : 0 ≤ E (fun d ↦ minCellLossVariance (KG d) (fun γ ↦ g (d, γ)) (τ d)) :=
    E.nonneg_eval _ (fun d ↦ minCellLossVariance_nonneg _ _ _ (hτpos d).le)
  have hlb := fixed_architecture_total_variance_lower_bound E KG KN g e τ hmean hτ
    hτpos
  have htot : 0 < variance (mixture E (fun d ↦ mixture (KG d) (fun _ ↦ KN d)))
      (fun z ↦ (g (z.1, z.2.1) + e (z.1, z.2.2)) ^ 2) := by linarith
  refine ⟨div_pos hB htot, ?_⟩
  rw [div_le_div_iff₀ htot (by linarith)]
  nlinarith

/-- The cell-wise two-point noise completion with a constant prescribed excess
`δ`, TQ (2.16): the skewness parameter is chosen per distance cell. -/
def completionNoise (KG : D → ExpFunctional G) (g : D × G → ℝ) (τ : D → ℝ)
    (hτpos : ∀ d, 0 < τ d) (δ : ℝ) (d : D) : ExpFunctional Bool :=
  zeroMeanNoise (τ d) (-2 * KG d (fun γ ↦ g (d, γ)) + Real.sqrt (δ / τ d))
    (hτpos d)

/-- The support values of the cell-wise two-point noise completion. -/
def completionNoiseValue (KG : D → ExpFunctional G) (g : D × G → ℝ) (τ : D → ℝ)
    (δ : ℝ) (z : D × Bool) : ℝ :=
  zeroMeanNoiseValue (τ z.1)
    (-2 * KG z.1 (fun γ ↦ g (z.1, γ)) + Real.sqrt (δ / τ z.1)) z.2

/-- The completion has the prescribed conditional noise variance in every cell,
so the whole conditional first/second-moment architecture is unchanged. -/
theorem completionNoise_conditional_moments (KG : D → ExpFunctional G)
    (g : D × G → ℝ) (τ : D → ℝ) (hτpos : ∀ d, 0 < τ d) (δ : ℝ) (d : D) :
    completionNoise KG g τ hτpos δ d
        (fun b ↦ completionNoiseValue KG g τ δ (d, b)) = 0 ∧
      completionNoise KG g τ hτpos δ d
        (fun b ↦ completionNoiseValue KG g τ δ (d, b) ^ 2) = τ d :=
  ⟨zeroMeanNoise_mean _ _ _, zeroMeanNoise_second _ _ _⟩

/-- The exact total loss variance of the two-point completion: `B + W₀ + δ`. -/
theorem completionNoise_total_loss_variance (E : ExpFunctional D)
    (KG : D → ExpFunctional G) (g : D × G → ℝ) (τ : D → ℝ)
    (hτpos : ∀ d, 0 < τ d) (δ : ℝ) (hδ : 0 ≤ δ) :
    variance (mixture E (fun d ↦ mixture (KG d)
          (fun _ ↦ completionNoise KG g τ hτpos δ d)))
        (fun z ↦ (g (z.1, z.2.1)
          + completionNoiseValue KG g τ δ (z.1, z.2.2)) ^ 2)
      = variance E (fun d ↦ KG d (fun γ ↦ g (d, γ) ^ 2) + τ d)
        + (E (fun d ↦ minCellLossVariance (KG d) (fun γ ↦ g (d, γ)) (τ d)) + δ) := by
  have hcell : ∀ d, variance (mixture (KG d)
      (fun _ ↦ completionNoise KG g τ hτpos δ d))
      (fun z ↦ (g (d, z.1) + completionNoiseValue KG g τ δ (d, z.2)) ^ 2)
      = minCellLossVariance (KG d) (fun γ ↦ g (d, γ)) (τ d) + δ := fun d ↦
    zeroMeanNoise_cell_loss_variance (KG d) (fun γ ↦ g (d, γ)) (τ d) δ (hτpos d) hδ
  rw [fixed_architecture_total_loss_variance E KG
    (fun d ↦ completionNoise KG g τ hτpos δ d) g (completionNoiseValue KG g τ δ) τ
    (fun d ↦ minCellLossVariance (KG d) (fun γ ↦ g (d, γ)) (τ d) + δ)
    (fun d ↦ (completionNoise_conditional_moments KG g τ hτpos δ d).1)
    (fun d ↦ (completionNoise_conditional_moments KG g τ hτpos δ d).2) hcell]
  have hsplit : (fun d ↦ minCellLossVariance (KG d) (fun γ ↦ g (d, γ)) (τ d) + δ)
      = (fun d ↦ minCellLossVariance (KG d) (fun γ ↦ g (d, γ)) (τ d))
        + (fun _ : D ↦ δ) := rfl
  rw [hsplit, E.add_eval, E.eval_const]

/-- Solving for the excess that realizes a prescribed explainable fraction. -/
theorem excess_for_fraction (b w η : ℝ) (hb : 0 < b) (hw : 0 ≤ w) (hη : 0 < η)
    (hle : η ≤ b / (b + w)) :
    0 ≤ b / η - b - w ∧ b / (b + (w + (b / η - b - w))) = η := by
  have hbw : 0 < b + w := by linarith
  have hne : η ≠ 0 := ne_of_gt hη
  have hbne : b ≠ 0 := ne_of_gt hb
  have h1 : η * (b + w) ≤ b := (le_div_iff₀ hbw).mp hle
  have h2 : (b + w) * η ≤ b := by nlinarith
  have h3 : b + w ≤ b / η := (le_div_iff₀ hη).mpr h2
  refine ⟨by linarith, ?_⟩
  have hd : b + (w + (b / η - b - w)) = b / η := by ring
  rw [hd, div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self hbne, mul_one]

/-- TQ Corollary 2.6: every value in `(0, B/(B+W₀)]` is attained by conditional
two-point noise, with the whole conditional first/second-moment architecture
held fixed. Together with `fixed_architecture_fraction_bounds` this is the exact
attainable interval, zero being an infimum that is not attained. -/
theorem fixed_architecture_fraction_attained (E : ExpFunctional D)
    (KG : D → ExpFunctional G) (g : D × G → ℝ) (τ : D → ℝ)
    (hτpos : ∀ d, 0 < τ d) (η : ℝ) (hη : 0 < η)
    (hB : 0 < variance E (fun d ↦ KG d (fun γ ↦ g (d, γ) ^ 2) + τ d))
    (hηle : η ≤ variance E (fun d ↦ KG d (fun γ ↦ g (d, γ) ^ 2) + τ d)
      / (variance E (fun d ↦ KG d (fun γ ↦ g (d, γ) ^ 2) + τ d)
        + E (fun d ↦ minCellLossVariance (KG d) (fun γ ↦ g (d, γ)) (τ d)))) :
    ∃ δ : ℝ, 0 ≤ δ ∧
      variance E (fun d ↦ KG d (fun γ ↦ g (d, γ) ^ 2) + τ d)
        / variance (mixture E (fun d ↦ mixture (KG d)
            (fun _ ↦ completionNoise KG g τ hτpos δ d)))
          (fun z ↦ (g (z.1, z.2.1)
            + completionNoiseValue KG g τ δ (z.1, z.2.2)) ^ 2) = η := by
  have hW0 : 0 ≤ E (fun d ↦ minCellLossVariance (KG d) (fun γ ↦ g (d, γ)) (τ d)) :=
    E.nonneg_eval _ (fun d ↦ minCellLossVariance_nonneg _ _ _ (hτpos d).le)
  obtain ⟨hδ, hfrac⟩ := excess_for_fraction _ _ η hB hW0 hη hηle
  refine ⟨_, hδ, ?_⟩
  rw [completionNoise_total_loss_variance E KG g τ hτpos _ hδ]
  exact hfrac

end

end Descent.Portability.LossNoiseCompletion
