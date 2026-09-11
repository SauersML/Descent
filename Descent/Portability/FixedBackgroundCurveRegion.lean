/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SourceFixedRealization

assert_below Descent.Decision Descent.Program

/-!
# The sharp fixed-background curve region

UPT Theorem 4.2 and PL Corollary 3.2.  Fix a genotype law carrying two centered,
unit-variance, uncorrelated observables `T` and `U` -- the manuscript's stated richness
condition, taken here as a hypothesis and then witnessed by two independent fair signs
so that nothing is vacuous.  Deploy `S = T`.  For arbitrary cellwise prescriptions
`v_d > 0`, `0 < H_d ≤ 1` and `0 ≤ q_d ≤ H_d`, the explicit phenotype of equation (4.3),

`Y = √v_d (√q_d T + √(H_d − q_d) U + √(1 − H_d) Z)`

with `Z` an independent fair environmental sign, has cellwise outcome variance exactly
`v_d`, cellwise genotype-explained fraction exactly `H_d`, and cellwise squared
correlation with the deployed score exactly `q_d`.  The genotype law, the deployed
score and the environmental law do not depend on the prescription, so one law realizes
the whole cellwise array at once.

Together with `AlignmentFactorization.scoreAccuracy_le_genotypeExplainedFraction` this
gives the exact region: at fixed `v_d, H_d` the attainable curve set is the Cartesian
product `∏_d [0, H_d]`, stated as `sharp_curve_region`.  This is the general form of the
three-coordinate `[0,H]` special case in `TraitPortabilityRange`.

Builds on `AlignmentFactorization.scoreAccuracy`,
`AlignmentFactorization.genotypeExplainedFraction`,
`AlignmentFactorization.regressionFunction`, `IndividualLossMoments.mixture`,
`SimultaneousRealization.shift_one`, `SimultaneousRealization.shift_sq`,
`SourceFixedRealization.uniformBool_eval` and `TraitPortabilityRange.sign`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FixedBackgroundCurveRegion

open Foundations IndividualLossMoments AlignmentFactorization SimultaneousRealization
open SourceFixedRealization

open TraitPortabilityRange (sign)

noncomputable section

variable {D Γ : Type*}

/-- The environmental term: a fair sign scaled by a prescribed amplitude.  It is
independent of the genotype and of the distance cell. -/
def envValue (c : ℝ) : Bool → ℝ := fun b ↦ c * sign b

/-- The environmental term has mean zero. -/
theorem env_mean (c : ℝ) : uniformExp Bool (envValue c) = 0 := by
  unfold envValue
  rw [uniformBool_eval, sign_false, sign_true]
  ring

/-- The environmental term has second moment `c²`. -/
theorem env_second (c : ℝ) : uniformExp Bool (fun b ↦ envValue c b ^ 2) = c ^ 2 := by
  unfold envValue
  rw [uniformBool_eval, sign_false, sign_true]
  ring

/-- The within-cell law: the unchanged genotype law together with an independent fair
environmental sign. -/
def backgroundLaw (G : ExpFunctional Γ) : ExpFunctional (Γ × Bool) :=
  mixture G (fun _ ↦ uniformExp Bool)

/-- The within-cell law is the genotype expectation of the environmental expectation. -/
theorem background_eval (G : ExpFunctional Γ) (f : Γ × Bool → ℝ) :
    backgroundLaw G f = G (fun g ↦ uniformExp Bool (fun b ↦ f (g, b))) := rfl

/-- Coefficient `√v_d √q_d` of the aligned genotype direction. -/
def curveA (v q : D → ℝ) (d : D) : ℝ := Real.sqrt (v d) * Real.sqrt (q d)

/-- Coefficient `√v_d √(H_d − q_d)` of the orthogonal genotype direction. -/
def curveB (v H q : D → ℝ) (d : D) : ℝ := Real.sqrt (v d) * Real.sqrt (H d - q d)

/-- Coefficient `√v_d √(1 − H_d)` of the environmental direction. -/
def curveC (v H : D → ℝ) (d : D) : ℝ := Real.sqrt (v d) * Real.sqrt (1 - H d)

/-- **The phenotype of UPT equation (4.3).** -/
def curvePhenotype (T U : Γ → ℝ) (v H q : D → ℝ) (d : D) : Γ × Bool → ℝ :=
  fun z ↦ curveA v q d * T z.1 + curveB v H q d * U z.1 + envValue (curveC v H d) z.2

/-- The phenotype written in the manuscript's grouped form `√v (√q T + √(H−q) U +
√(1−H) Z)`. -/
theorem curvePhenotype_grouped (T U : Γ → ℝ) (v H q : D → ℝ) (d : D) (z : Γ × Bool) :
    curvePhenotype T U v H q d z
      = Real.sqrt (v d) * (Real.sqrt (q d) * T z.1
          + Real.sqrt (H d - q d) * U z.1 + Real.sqrt (1 - H d) * sign z.2) := by
  unfold curvePhenotype curveA curveB curveC envValue
  ring

/-- The aligned coefficient squares to `v_d q_d`. -/
theorem curveA_sq (v q : D → ℝ) (d : D) (hv : 0 ≤ v d) (hq : 0 ≤ q d) :
    curveA v q d ^ 2 = v d * q d := by
  unfold curveA
  rw [mul_pow, Real.sq_sqrt hv, Real.sq_sqrt hq]

/-- The orthogonal coefficient squares to `v_d (H_d − q_d)`. -/
theorem curveB_sq (v H q : D → ℝ) (d : D) (hv : 0 ≤ v d) (hqH : q d ≤ H d) :
    curveB v H q d ^ 2 = v d * (H d - q d) := by
  unfold curveB
  rw [mul_pow, Real.sq_sqrt hv, Real.sq_sqrt (by linarith : (0:ℝ) ≤ H d - q d)]

/-- The environmental coefficient squares to `v_d (1 − H_d)`. -/
theorem curveC_sq (v H : D → ℝ) (d : D) (hv : 0 ≤ v d) (hH1 : H d ≤ 1) :
    curveC v H d ^ 2 = v d * (1 - H d) := by
  unfold curveC
  rw [mul_pow, Real.sq_sqrt hv, Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 - H d)]

/-! ### Moments on an arbitrary orthonormal genotype pair -/

/-- A genotype contrast built from two centered observables has mean zero. -/
theorem pair_mean (G : ExpFunctional Γ) (T U : Γ → ℝ) (hT : G T = 0) (hU : G U = 0)
    (A B : ℝ) : G (fun g ↦ A * T g + B * U g) = 0 := by
  have hsplit : (fun g ↦ A * T g + B * U g) = (A • T) + (B • U) := by
    funext g
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsplit, G.add_eval, G.smul_eval, G.smul_eval, hT, hU]
  ring

/-- A genotype contrast built from an orthonormal pair has second moment `A² + B²`. -/
theorem pair_second (G : ExpFunctional Γ) (T U : Γ → ℝ)
    (hT2 : G (fun g ↦ T g ^ 2) = 1) (hU2 : G (fun g ↦ U g ^ 2) = 1)
    (hTU : G (fun g ↦ T g * U g) = 0) (A B : ℝ) :
    G (fun g ↦ (A * T g + B * U g) ^ 2) = A ^ 2 + B ^ 2 := by
  have hsplit : (fun g ↦ (A * T g + B * U g) ^ 2)
      = ((A ^ 2) • fun g ↦ T g ^ 2) + ((2 * A * B) • fun g ↦ T g * U g)
        + ((B ^ 2) • fun g ↦ U g ^ 2) := by
    funext g
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit, G.add_eval, G.add_eval, G.smul_eval, G.smul_eval, G.smul_eval, hT2, hTU,
    hU2]
  ring

/-- The deployed observable reads its own coefficient off a contrast. -/
theorem pair_cross (G : ExpFunctional Γ) (T U : Γ → ℝ)
    (hT2 : G (fun g ↦ T g ^ 2) = 1) (hTU : G (fun g ↦ T g * U g) = 0) (A B : ℝ) :
    G (fun g ↦ T g * (A * T g + B * U g)) = A := by
  have hsplit : (fun g ↦ T g * (A * T g + B * U g))
      = (A • fun g ↦ T g ^ 2) + (B • fun g ↦ T g * U g) := by
    funext g
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit, G.add_eval, G.smul_eval, G.smul_eval, hT2, hTU]
  ring

/-! ### The cellwise moments of the prescribed phenotype -/

/-- **Conditioning on the genotype removes exactly the environmental term.** -/
theorem curve_regression_function (T U : Γ → ℝ) (v H q : D → ℝ) (d : D) :
    regressionFunction (fun _ : Γ ↦ uniformExp Bool) (curvePhenotype T U v H q d)
      = fun g : Γ ↦ curveA v q d * T g + curveB v H q d * U g := by
  funext g
  show uniformExp Bool
      (fun b ↦ (curveA v q d * T g + curveB v H q d * U g) + envValue (curveC v H d) b)
    = curveA v q d * T g + curveB v H q d * U g
  rw [shift_one, env_mean]
  ring

/-- The cellwise phenotype mean is zero. -/
theorem curve_mean (G : ExpFunctional Γ) (T U : Γ → ℝ) (hT : G T = 0) (hU : G U = 0)
    (v H q : D → ℝ) (d : D) :
    backgroundLaw G (curvePhenotype T U v H q d) = 0 := by
  have hreg : backgroundLaw G (curvePhenotype T U v H q d)
      = G (regressionFunction (fun _ : Γ ↦ uniformExp Bool)
        (curvePhenotype T U v H q d)) := rfl
  rw [hreg, curve_regression_function, pair_mean G T U hT hU]

/-- **The cellwise outcome variance is exactly the prescribed `v_d`.** -/
theorem curve_variance (G : ExpFunctional Γ) (T U : Γ → ℝ) (hT : G T = 0) (hU : G U = 0)
    (hT2 : G (fun g ↦ T g ^ 2) = 1) (hU2 : G (fun g ↦ U g ^ 2) = 1)
    (hTU : G (fun g ↦ T g * U g) = 0) (v H q : D → ℝ) (d : D) (hv : 0 ≤ v d)
    (hq0 : 0 ≤ q d) (hqH : q d ≤ H d) (hH1 : H d ≤ 1) :
    variance (backgroundLaw G) (curvePhenotype T U v H q d) = v d := by
  have hsq : backgroundLaw G (fun z ↦ curvePhenotype T U v H q d z ^ 2)
      = curveA v q d ^ 2 + curveB v H q d ^ 2 + curveC v H d ^ 2 := by
    have hinner : (fun g : Γ ↦ uniformExp Bool
        (fun b ↦ curvePhenotype T U v H q d (g, b) ^ 2))
        = fun g : Γ ↦ (curveA v q d * T g + curveB v H q d * U g) ^ 2
            + curveC v H d ^ 2 := by
      funext g
      show uniformExp Bool (fun b ↦
          ((curveA v q d * T g + curveB v H q d * U g) + envValue (curveC v H d) b) ^ 2)
        = (curveA v q d * T g + curveB v H q d * U g) ^ 2 + curveC v H d ^ 2
      rw [shift_sq, env_mean, env_second]
      ring
    rw [background_eval, hinner, eval_add_const, pair_second G T U hT2 hU2 hTU]
  rw [variance_eq_expect_sq_sub_sq_mean, curve_mean G T U hT hU, hsq,
    curveA_sq v q d hv hq0, curveB_sq v H q d hv hqH, curveC_sq v H d hv hH1]
  ring

/-- **The cellwise genotype-explained variance fraction is exactly the prescribed
`H_d`.** -/
theorem curve_genotype_fraction (G : ExpFunctional Γ) (T U : Γ → ℝ) (hT : G T = 0)
    (hU : G U = 0) (hT2 : G (fun g ↦ T g ^ 2) = 1) (hU2 : G (fun g ↦ U g ^ 2) = 1)
    (hTU : G (fun g ↦ T g * U g) = 0) (v H q : D → ℝ) (d : D) (hv : 0 < v d)
    (hq0 : 0 ≤ q d) (hqH : q d ≤ H d) (hH1 : H d ≤ 1) :
    genotypeExplainedFraction G (fun _ : Γ ↦ uniformExp Bool)
      (curvePhenotype T U v H q d) = H d := by
  have hlaw : mixture G (fun _ : Γ ↦ uniformExp Bool) = backgroundLaw G := rfl
  have hgen : variance G (regressionFunction (fun _ : Γ ↦ uniformExp Bool)
      (curvePhenotype T U v H q d)) = v d * H d := by
    rw [curve_regression_function, variance_eq_expect_sq_sub_sq_mean,
      pair_mean G T U hT hU, pair_second G T U hT2 hU2 hTU,
      curveA_sq v q d hv.le hq0, curveB_sq v H q d hv.le hqH]
    ring
  unfold genotypeExplainedFraction explainableFraction Descent.Core.ratio
  rw [hgen, hlaw, curve_variance G T U hT hU hT2 hU2 hTU v H q d hv.le hq0 hqH hH1]
  field_simp

/-- **The cellwise squared correlation with the deployed score is exactly the prescribed
`q_d`.** -/
theorem curve_score_accuracy (G : ExpFunctional Γ) (T U : Γ → ℝ) (hT : G T = 0)
    (hU : G U = 0) (hT2 : G (fun g ↦ T g ^ 2) = 1) (hU2 : G (fun g ↦ U g ^ 2) = 1)
    (hTU : G (fun g ↦ T g * U g) = 0) (v H q : D → ℝ) (d : D) (hv : 0 < v d)
    (hq0 : 0 ≤ q d) (hqH : q d ≤ H d) (hH1 : H d ≤ 1) :
    scoreAccuracy G (fun _ : Γ ↦ uniformExp Bool) T (curvePhenotype T U v H q d)
      = q d := by
  have hlaw : mixture G (fun _ : Γ ↦ uniformExp Bool) = backgroundLaw G := rfl
  have hvarT : variance G T = 1 := by
    rw [variance_eq_expect_sq_sub_sq_mean, hT, hT2]
    ring
  have hcov : covariance (mixture G (fun _ : Γ ↦ uniformExp Bool))
      (liftGenotype (Ω := Bool) T) (curvePhenotype T U v H q d) = curveA v q d := by
    rw [mixture_covariance_liftGenotype, curve_regression_function,
      covariance_eq_expect_mul_sub_means, hT, pair_mean G T U hT hU,
      pair_cross G T U hT2 hTU]
    ring
  unfold scoreAccuracy
  rw [hcov, hvarT, hlaw,
    curve_variance G T U hT hU hT2 hU2 hTU v H q d hv.le hq0 hqH hH1,
    curveA_sq v q d hv.le hq0]
  field_simp

/-- **UPT Theorem 4.2 / PL Corollary 3.2: the prescribed cellwise curve is realized
exactly on an unchanged genetic background.**  All three conclusions of equation (4.2)
at once, for a single phenotype law covering every cell. -/
theorem fixed_background_curve_realized (G : ExpFunctional Γ) (T U : Γ → ℝ)
    (hT : G T = 0) (hU : G U = 0) (hT2 : G (fun g ↦ T g ^ 2) = 1)
    (hU2 : G (fun g ↦ U g ^ 2) = 1) (hTU : G (fun g ↦ T g * U g) = 0) (v H q : D → ℝ)
    (hv : ∀ d, 0 < v d) (hq0 : ∀ d, 0 ≤ q d) (hqH : ∀ d, q d ≤ H d)
    (hH1 : ∀ d, H d ≤ 1) :
    ∀ d : D,
      variance (backgroundLaw G) (curvePhenotype T U v H q d) = v d ∧
        genotypeExplainedFraction G (fun _ : Γ ↦ uniformExp Bool)
            (curvePhenotype T U v H q d) = H d ∧
          scoreAccuracy G (fun _ : Γ ↦ uniformExp Bool) T
            (curvePhenotype T U v H q d) = q d :=
  fun d ↦
    ⟨curve_variance G T U hT hU hT2 hU2 hTU v H q d (hv d).le (hq0 d) (hqH d) (hH1 d),
      curve_genotype_fraction G T U hT hU hT2 hU2 hTU v H q d (hv d) (hq0 d) (hqH d)
        (hH1 d),
      curve_score_accuracy G T U hT hU hT2 hU2 hTU v H q d (hv d) (hq0 d) (hqH d)
        (hH1 d)⟩

/-- **The exact curve region is the Cartesian product `∏_d [0, H_d]`.**  Attainment is
the explicit construction; necessity is the alignment factorization, which bounds every
cellwise squared correlation by the cellwise genotype-explained fraction. -/
theorem sharp_curve_region (G : ExpFunctional Γ) (T U : Γ → ℝ) (hT : G T = 0)
    (hU : G U = 0) (hT2 : G (fun g ↦ T g ^ 2) = 1) (hU2 : G (fun g ↦ U g ^ 2) = 1)
    (hTU : G (fun g ↦ T g * U g) = 0) (v H q : D → ℝ) (hv : ∀ d, 0 < v d)
    (hH1 : ∀ d, H d ≤ 1) :
    (∀ d, 0 ≤ q d ∧ q d ≤ H d) ↔
      (∀ d : D,
        variance (backgroundLaw G) (curvePhenotype T U v H q d) = v d ∧
          genotypeExplainedFraction G (fun _ : Γ ↦ uniformExp Bool)
              (curvePhenotype T U v H q d) = H d ∧
            scoreAccuracy G (fun _ : Γ ↦ uniformExp Bool) T
              (curvePhenotype T U v H q d) = q d) := by
  constructor
  · intro hq
    exact fixed_background_curve_realized G T U hT hU hT2 hU2 hTU v H q hv
      (fun d ↦ (hq d).1) (fun d ↦ (hq d).2) hH1
  · intro hreal d
    obtain ⟨hvar, hgen, hacc⟩ := hreal d
    have hvarT : 0 < variance G T := by
      rw [variance_eq_expect_sq_sub_sq_mean, hT, hT2]
      norm_num
    have hvarY : 0 < variance (mixture G (fun _ : Γ ↦ uniformExp Bool))
        (curvePhenotype T U v H q d) := by
      have hlaw : mixture G (fun _ : Γ ↦ uniformExp Bool) = backgroundLaw G := rfl
      rw [hlaw, hvar]
      exact hv d
    obtain ⟨hpos, hle, _⟩ := scoreAccuracy_le_genotypeExplainedFraction G
      (fun _ : Γ ↦ uniformExp Bool) T (curvePhenotype T U v H q d) hvarT hvarY
    rw [hacc] at hpos hle
    rw [hgen] at hle
    exact ⟨hpos, hle⟩

/-! ### The richness condition is satisfiable -/

/-- Two independent fair scored signs are a centered, unit-variance, uncorrelated
genotype pair: the richness condition of UPT Theorem 4.2 is not vacuous. -/
theorem rademacher_pair_witness :
    uniformExp (Bool × Bool) (fun g ↦ sign g.1) = 0 ∧
      uniformExp (Bool × Bool) (fun g ↦ sign g.2) = 0 ∧
        uniformExp (Bool × Bool) (fun g ↦ sign g.1 ^ 2) = 1 ∧
          uniformExp (Bool × Bool) (fun g ↦ sign g.2 ^ 2) = 1 ∧
            uniformExp (Bool × Bool) (fun g ↦ sign g.1 * sign g.2) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [uniformExp_apply, Fintype.sum_prod_type, Fintype.sum_bool, sign]

/-- **PL Corollary 3.2 verbatim: two independent fair signs, unit outcome variance.**
On the fixed pair of scored signs with `S = G₁`, the phenotype
`√q G₁ + √(h − q) G₂ + √(1 − h) Z` has outcome variance one, genotype-predictable
fraction `h(d)` and squared score correlation exactly `q(d)` in every stratum. -/
theorem unit_variance_curve_realized (h q : D → ℝ) (hq0 : ∀ d, 0 ≤ q d)
    (hqh : ∀ d, q d ≤ h d) (hh1 : ∀ d, h d ≤ 1) :
    ∀ d : D,
      variance (backgroundLaw (uniformExp (Bool × Bool)))
          (curvePhenotype (fun g ↦ sign g.1) (fun g ↦ sign g.2) (fun _ ↦ 1) h q d)
          = 1 ∧
        genotypeExplainedFraction (uniformExp (Bool × Bool))
            (fun _ : Bool × Bool ↦ uniformExp Bool)
            (curvePhenotype (fun g ↦ sign g.1) (fun g ↦ sign g.2) (fun _ ↦ 1) h q d)
            = h d ∧
          scoreAccuracy (uniformExp (Bool × Bool))
            (fun _ : Bool × Bool ↦ uniformExp Bool) (fun g ↦ sign g.1)
            (curvePhenotype (fun g ↦ sign g.1) (fun g ↦ sign g.2) (fun _ ↦ 1) h q d)
            = q d := by
  obtain ⟨hT, hU, hT2, hU2, hTU⟩ := rademacher_pair_witness
  exact fixed_background_curve_realized (uniformExp (Bool × Bool)) (fun g ↦ sign g.1)
    (fun g ↦ sign g.2) hT hU hT2 hU2 hTU (fun _ ↦ 1) h q (fun _ ↦ one_pos) hq0 hqh hh1

end

end Descent.Portability.FixedBackgroundCurveRegion
