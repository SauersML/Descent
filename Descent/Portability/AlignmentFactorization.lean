/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IndividualLossMoments

assert_below Descent.Decision Descent.Program

/-!
# Exact alignment factorization: signal magnitude is not alignment

A genotype law on `G` and a conditional outcome kernel `K : G → ExpFunctional Ω`
generate the joint law `IndividualLossMoments.mixture E K`.  The genotype regression
function `g γ = K γ (Y (γ, ·))` is then *computed* from that kernel rather than
postulated, so the manuscript's hypothesis `E[ε ∣ G] = 0` is a theorem here and not an
assumption: `mixture_covariance_liftGenotype` derives the orthogonality of the
conditional residual to every genotype observable.

Proved: the exact factorization `q = H ρ²` (UPT Theorem 4.1 equation (4.1), PL Theorem
3.1 equation (3.1)), where `H` is the genotype-explained variance fraction
`Var(g)/Var(Y)` and `ρ²` the squared correlation of the deployed score with `g`; the
chain `0 ≤ q ≤ H ≤ 1`; the degenerate branch `Var(g) = 0 ⇒ q = 0`; and the exact
equality condition, `q = H` precisely when the centered regression function is a
nonzero multiple of the centered score in the almost-everywhere sense a positive linear
functional supports.

Builds on `Foundations.variance`, `Foundations.covariance`,
`Foundations.ExpFunctional.cauchy_schwarz`, `Foundations.explainableFraction` and
`IndividualLossMoments.total_variance`.

## Empirical status

None. The bodies here are algebra: a factorization of a squared correlation is a statement about a
law, not about a cohort.  What carries an empirical status is a named
quantity in a subsystem module asserting that this algebra computes something
measurable, and such names keep their own docstrings, regimes and ledger rows.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AlignmentFactorization

open Foundations IndividualLossMoments

noncomputable section

variable {G Ω : Type*}

/-- The genotype regression function `g(γ) = E[Y ∣ G = γ]`, read off the conditional
outcome kernel.  Nothing is assumed about it: it is the kernel's own mean. -/
def regressionFunction (K : G → ExpFunctional Ω) (Y : G × Ω → ℝ) : G → ℝ :=
  fun γ ↦ K γ (fun ω ↦ Y (γ, ω))

/-- A genotype-measurable observable read on the joint space.  A deployed polygenic
score is one of these: a function of the genotype alone. -/
def liftGenotype (S : G → ℝ) : G × Ω → ℝ := fun z ↦ S z.1

/-- The joint mean of a genotype observable is its genotype-law mean. -/
theorem mixture_eval_liftGenotype (E : ExpFunctional G) (K : G → ExpFunctional Ω)
    (S : G → ℝ) : mixture E K (liftGenotype (Ω := Ω) S) = E S := by
  change E (fun γ ↦ K γ (fun _ ↦ S γ)) = E S
  simp only [ExpFunctional.eval_const]

/-- The joint variance of a genotype observable is its genotype-law variance. -/
theorem mixture_variance_liftGenotype (E : ExpFunctional G) (K : G → ExpFunctional Ω)
    (S : G → ℝ) :
    variance (mixture E K) (liftGenotype (Ω := Ω) S) = variance E S := by
  rw [variance_eq_expect_sq_sub_sq_mean, variance_eq_expect_sq_sub_sq_mean,
    mixture_eval_liftGenotype]
  congr 1
  have hsq : (fun z : G × Ω ↦ liftGenotype (Ω := Ω) S z ^ 2)
      = liftGenotype (Ω := Ω) (fun γ ↦ S γ ^ 2) := rfl
  rw [hsq, mixture_eval_liftGenotype]

/-- **Conditional orthogonality, derived.**  The covariance of a genotype observable
with the outcome is its covariance with the regression function: what the kernel
randomises away contributes nothing.  This is the manuscript's
`Cov(S,Y) = E[(S - E S) g]`, proved from the kernel rather than assumed. -/
theorem mixture_covariance_liftGenotype (E : ExpFunctional G) (K : G → ExpFunctional Ω)
    (S : G → ℝ) (Y : G × Ω → ℝ) :
    covariance (mixture E K) (liftGenotype (Ω := Ω) S) Y
      = covariance E S (regressionFunction K Y) := by
  have hprod : ∀ γ : G, K γ (fun ω ↦ S γ * Y (γ, ω))
      = S γ * regressionFunction K Y γ := by
    intro γ
    have hfun : (fun ω ↦ S γ * Y (γ, ω)) = (S γ) • (fun ω ↦ Y (γ, ω)) := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [hfun, (K γ).smul_eval]
    rfl
  have hmean : mixture E K Y = E (regressionFunction K Y) := rfl
  rw [covariance_eq_expect_mul_sub_means, covariance_eq_expect_mul_sub_means,
    mixture_eval_liftGenotype, hmean]
  congr 1
  change E (fun γ ↦ K γ (fun ω ↦ S γ * Y (γ, ω)))
    = E (fun γ ↦ S γ * regressionFunction K Y γ)
  exact congrArg (fun f ↦ E f) (funext hprod)

/-- The genotype-explained variance fraction `H = Var(E[Y ∣ G]) / Var(Y)`.  It equals an
additive genetic variance fraction only in an additive model with an orthogonal
residual; in general it is the predictable fraction and nothing more. -/
def genotypeExplainedFraction (E : ExpFunctional G) (K : G → ExpFunctional Ω)
    (Y : G × Ω → ℝ) : ℝ :=
  explainableFraction (variance E (regressionFunction K Y)) (variance (mixture E K) Y)

/-- The deployed score's squared correlation with the outcome, `q`. -/
def scoreAccuracy (E : ExpFunctional G) (K : G → ExpFunctional Ω) (S : G → ℝ)
    (Y : G × Ω → ℝ) : ℝ :=
  covariance (mixture E K) (liftGenotype (Ω := Ω) S) Y ^ 2 /
    (variance E S * variance (mixture E K) Y)

/-- The alignment `ρ²`: squared correlation between the deployed score and the genotype
regression function, in genotype-function space. -/
def alignmentSquared (E : ExpFunctional G) (K : G → ExpFunctional Ω) (S : G → ℝ)
    (Y : G × Ω → ℝ) : ℝ :=
  covariance E S (regressionFunction K Y) ^ 2 /
    (variance E S * variance E (regressionFunction K Y))

/-- Variance is nonnegative for a positive linear functional. -/
theorem variance_nonneg (E : ExpFunctional G) (f : G → ℝ) : 0 ≤ variance E f :=
  E.nonneg_eval _ fun _ ↦ sq_nonneg _

/-- Cauchy-Schwarz in covariance form, on the centered observables. -/
theorem covariance_sq_le (E : ExpFunctional G) (f h : G → ℝ) :
    covariance E f h ^ 2 ≤ variance E f * variance E h :=
  ExpFunctional.cauchy_schwarz E (fun γ ↦ f γ - E f) (fun γ ↦ h γ - E h)

/-- The mean square of the alignment defect, expanded in the second moments. -/
theorem alignment_defect_expand (E : ExpFunctional G) (S g : G → ℝ) (lam : ℝ) :
    E (fun γ ↦ ((g γ - E g) - lam * (S γ - E S)) ^ 2)
      = variance E g - 2 * lam * covariance E S g + lam ^ 2 * variance E S := by
  have hsplit : (fun γ ↦ ((g γ - E g) - lam * (S γ - E S)) ^ 2)
      = (fun γ ↦ (g γ - E g) ^ 2)
        + ((-(2 * lam)) • fun γ ↦ (S γ - E S) * (g γ - E g))
        + ((lam ^ 2) • fun γ ↦ (S γ - E S) ^ 2) := by
    funext γ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit, E.add_eval, E.add_eval, E.smul_eval, E.smul_eval]
  unfold variance covariance
  ring

/-- The score read against the alignment defect. -/
theorem alignment_defect_score_inner (E : ExpFunctional G) (S g : G → ℝ) (lam : ℝ) :
    E (fun γ ↦ (S γ - E S) * ((g γ - E g) - lam * (S γ - E S)))
      = covariance E S g - lam * variance E S := by
  have hsplit : (fun γ ↦ (S γ - E S) * ((g γ - E g) - lam * (S γ - E S)))
      = (fun γ ↦ (S γ - E S) * (g γ - E g))
        + ((-lam) • fun γ ↦ (S γ - E S) ^ 2) := by
    funext γ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit, E.add_eval, E.smul_eval]
  unfold variance covariance
  ring

/-- The regression function read against the alignment defect. -/
theorem alignment_defect_regression_inner (E : ExpFunctional G) (S g : G → ℝ) (lam : ℝ) :
    E (fun γ ↦ (g γ - E g) * ((g γ - E g) - lam * (S γ - E S)))
      = variance E g - lam * covariance E S g := by
  have hsplit : (fun γ ↦ (g γ - E g) * ((g γ - E g) - lam * (S γ - E S)))
      = (fun γ ↦ (g γ - E g) ^ 2)
        + ((-lam) • fun γ ↦ (S γ - E S) * (g γ - E g)) := by
    funext γ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit, E.add_eval, E.smul_eval]
  unfold variance covariance
  ring

/-- **UPT Theorem 4.1 / PL Theorem 3.1, equation (4.1)/(3.1): exact alignment
factorization.**  Squared correlation with the outcome is the genotype-explained
variance fraction times the squared correlation with the regression function.  The
only hypothesis is that the regression function is nonconstant, the domain condition
that makes `ρ²` a number at all. -/
theorem alignment_factorisation (E : ExpFunctional G) (K : G → ExpFunctional Ω)
    (S : G → ℝ) (Y : G × Ω → ℝ)
    (hg : variance E (regressionFunction K Y) ≠ 0) :
    scoreAccuracy E K S Y
      = genotypeExplainedFraction E K Y * alignmentSquared E K S Y := by
  unfold scoreAccuracy genotypeExplainedFraction alignmentSquared explainableFraction
    Descent.Core.ratio
  rw [mixture_covariance_liftGenotype]
  rcases eq_or_ne (variance E S) 0 with hS | hS
  · rw [hS]
    simp
  · rcases eq_or_ne (variance (mixture E K) Y) 0 with hY | hY
    · rw [hY]
      simp
    · field_simp

/-- The genotype-explained fraction is nonnegative. -/
theorem genotypeExplainedFraction_nonneg (E : ExpFunctional G) (K : G → ExpFunctional Ω)
    (Y : G × Ω → ℝ) : 0 ≤ genotypeExplainedFraction E K Y := by
  unfold genotypeExplainedFraction explainableFraction Descent.Core.ratio
  exact div_nonneg (variance_nonneg _ _) (variance_nonneg _ _)

/-- **`H ≤ 1`.**  The regression function's variance is one part of the outcome
variance, the other being the mean conditional variance the kernel supplies. -/
theorem genotypeExplainedFraction_le_one (E : ExpFunctional G) (K : G → ExpFunctional Ω)
    (Y : G × Ω → ℝ) (hY : 0 < variance (mixture E K) Y) :
    genotypeExplainedFraction E K Y ≤ 1 := by
  have hwithin : 0 ≤ E (fun γ ↦ variance (K γ) (fun ω ↦ Y (γ, ω))) :=
    E.nonneg_eval _ fun γ ↦ variance_nonneg _ _
  have htot := total_variance E K Y
  unfold genotypeExplainedFraction explainableFraction Descent.Core.ratio
    regressionFunction
  rw [div_le_one hY]
  linarith

/-- Alignment is nonnegative. -/
theorem alignmentSquared_nonneg (E : ExpFunctional G) (K : G → ExpFunctional Ω)
    (S : G → ℝ) (Y : G × Ω → ℝ) : 0 ≤ alignmentSquared E K S Y :=
  div_nonneg (sq_nonneg _) (mul_nonneg (variance_nonneg _ _) (variance_nonneg _ _))

/-- **`ρ² ≤ 1`.**  Cauchy-Schwarz in genotype-function space. -/
theorem alignmentSquared_le_one (E : ExpFunctional G) (K : G → ExpFunctional Ω)
    (S : G → ℝ) (Y : G × Ω → ℝ) (hS : 0 < variance E S)
    (hg : 0 < variance E (regressionFunction K Y)) :
    alignmentSquared E K S Y ≤ 1 := by
  unfold alignmentSquared
  rw [div_le_one (by positivity)]
  exact covariance_sq_le E S (regressionFunction K Y)

/-- `q` is nonnegative. -/
theorem scoreAccuracy_nonneg (E : ExpFunctional G) (K : G → ExpFunctional Ω)
    (S : G → ℝ) (Y : G × Ω → ℝ) : 0 ≤ scoreAccuracy E K S Y :=
  div_nonneg (sq_nonneg _) (mul_nonneg (variance_nonneg _ _) (variance_nonneg _ _))

/-- **The degenerate branch of UPT Theorem 4.1: `H = 0 ⇒ q = 0`.**  A genotype that
predicts nothing leaves every score with zero squared correlation, whatever the score
is.  Proved from Cauchy-Schwarz, not by a continuity argument. -/
theorem scoreAccuracy_eq_zero_of_no_genotype_signal (E : ExpFunctional G)
    (K : G → ExpFunctional Ω) (S : G → ℝ) (Y : G × Ω → ℝ)
    (hg : variance E (regressionFunction K Y) = 0) : scoreAccuracy E K S Y = 0 := by
  have hcs := covariance_sq_le E S (regressionFunction K Y)
  rw [hg, mul_zero] at hcs
  have hsq : covariance E S (regressionFunction K Y) ^ 2 = 0 :=
    le_antisymm hcs (sq_nonneg _)
  have hzero : covariance E S (regressionFunction K Y) = 0 := by
    by_contra hne
    exact absurd hsq (pow_ne_zero 2 hne)
  unfold scoreAccuracy
  rw [mixture_covariance_liftGenotype, hzero]
  simp

/-- **UPT Theorem 4.1, the chain `0 ≤ q ≤ H ≤ 1`.**  Heritability-like information
bounds the length of the predictable component; a score's accuracy is that length
scaled by an alignment the length does not determine. -/
theorem scoreAccuracy_le_genotypeExplainedFraction (E : ExpFunctional G)
    (K : G → ExpFunctional Ω) (S : G → ℝ) (Y : G × Ω → ℝ)
    (hS : 0 < variance E S) (hY : 0 < variance (mixture E K) Y) :
    0 ≤ scoreAccuracy E K S Y ∧
      scoreAccuracy E K S Y ≤ genotypeExplainedFraction E K Y ∧
      genotypeExplainedFraction E K Y ≤ 1 := by
  refine ⟨scoreAccuracy_nonneg E K S Y, ?_, genotypeExplainedFraction_le_one E K Y hY⟩
  rcases eq_or_lt_of_le (variance_nonneg E (regressionFunction K Y)) with hg | hg
  · rw [scoreAccuracy_eq_zero_of_no_genotype_signal E K S Y hg.symm]
    exact genotypeExplainedFraction_nonneg E K Y
  · rw [alignment_factorisation E K S Y hg.ne']
    calc genotypeExplainedFraction E K Y * alignmentSquared E K S Y
        ≤ genotypeExplainedFraction E K Y * 1 :=
          mul_le_mul_of_nonneg_left (alignmentSquared_le_one E K S Y hS hg)
            (genotypeExplainedFraction_nonneg E K Y)
      _ = genotypeExplainedFraction E K Y := mul_one _

/-- **The Cauchy-Schwarz equality case, in the almost-everywhere form a positive linear
functional supports.**  `Cov(S,g)² = Var(S) Var(g)` exactly when the centered regression
function is a nonzero multiple of the centered score up to an observable of zero mean
square.  Both variances nonzero is the manuscript's `H > 0` with a nonconstant score. -/
theorem alignment_equality_iff (E : ExpFunctional G) (K : G → ExpFunctional Ω)
    (S : G → ℝ) (Y : G × Ω → ℝ) (hS : variance E S ≠ 0)
    (hg : variance E (regressionFunction K Y) ≠ 0) :
    covariance E S (regressionFunction K Y) ^ 2
        = variance E S * variance E (regressionFunction K Y) ↔
      ∃ lam : ℝ, lam ≠ 0 ∧
        E (fun γ ↦ ((regressionFunction K Y γ - E (regressionFunction K Y))
          - lam * (S γ - E S)) ^ 2) = 0 := by
  have hupos : 0 < variance E S := lt_of_le_of_ne (variance_nonneg E S) (Ne.symm hS)
  constructor
  · intro heq
    refine ⟨covariance E S (regressionFunction K Y) / variance E S, ?_, ?_⟩
    · have hc : covariance E S (regressionFunction K Y) ≠ 0 := by
        intro hc0
        have hz : variance E S * variance E (regressionFunction K Y) = 0 := by
          rw [← heq, hc0]
          ring
        rcases mul_eq_zero.mp hz with h | h
        · exact hS h
        · exact hg h
      exact div_ne_zero hc hupos.ne'
    · rw [alignment_defect_expand]
      field_simp
      nlinarith [heq]
  · rintro ⟨lam, hlam, hzero⟩
    have hS2 := ExpFunctional.cauchy_schwarz E (fun γ ↦ S γ - E S)
      (fun γ ↦ (regressionFunction K Y γ - E (regressionFunction K Y))
        - lam * (S γ - E S))
    have hg2 := ExpFunctional.cauchy_schwarz E
      (fun γ ↦ regressionFunction K Y γ - E (regressionFunction K Y))
      (fun γ ↦ (regressionFunction K Y γ - E (regressionFunction K Y))
        - lam * (S γ - E S))
    rw [hzero, mul_zero, alignment_defect_score_inner] at hS2
    rw [hzero, mul_zero, alignment_defect_regression_inner] at hg2
    have hc : covariance E S (regressionFunction K Y) = lam * variance E S := by
      nlinarith [sq_nonneg (covariance E S (regressionFunction K Y)
        - lam * variance E S)]
    have hv : variance E (regressionFunction K Y)
        = lam * covariance E S (regressionFunction K Y) := by
      nlinarith [sq_nonneg (variance E (regressionFunction K Y)
        - lam * covariance E S (regressionFunction K Y))]
    rw [hc, hv, hc]
    ring

/-- **The equality case of UPT Theorem 4.1.**  `q = H` exactly when the regression
function is a nonzero multiple of the centered score almost everywhere: full accuracy
relative to the available genetic signal is alignment one, and says nothing about the
magnitude of that signal. -/
theorem accuracy_attains_genotype_fraction_iff (E : ExpFunctional G)
    (K : G → ExpFunctional Ω) (S : G → ℝ) (Y : G × Ω → ℝ)
    (hS : variance E S ≠ 0) (hg : variance E (regressionFunction K Y) ≠ 0)
    (hY : 0 < variance (mixture E K) Y) :
    scoreAccuracy E K S Y = genotypeExplainedFraction E K Y ↔
      ∃ lam : ℝ, lam ≠ 0 ∧
        E (fun γ ↦ ((regressionFunction K Y γ - E (regressionFunction K Y))
          - lam * (S γ - E S)) ^ 2) = 0 := by
  have hHpos : 0 < genotypeExplainedFraction E K Y := by
    unfold genotypeExplainedFraction explainableFraction Descent.Core.ratio
    exact div_pos (lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hg)) hY
  rw [← alignment_equality_iff E K S Y hS hg, alignment_factorisation E K S Y hg]
  constructor
  · intro heq
    have hone : alignmentSquared E K S Y = 1 :=
      mul_left_cancel₀ hHpos.ne' (by rw [mul_one]; exact heq)
    unfold alignmentSquared at hone
    have hval := (div_eq_iff (mul_ne_zero hS hg)).mp hone
    rw [one_mul] at hval
    exact hval
  · intro heq
    have hone : alignmentSquared E K S Y = 1 := by
      unfold alignmentSquared
      rw [heq]
      exact div_self (mul_ne_zero hS hg)
    rw [hone, mul_one]

end

end Descent.Portability.AlignmentFactorization
