/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MomentOrderObstruction
import Descent.Portability.FiniteGeneticTransition
import Descent.Portability.SquaredCorrelationZeroTest
import Mathlib.Algebra.Polynomial.BigOperators

assert_below Descent.Decision Descent.Program

/-!
# A one-parameter score/outcome family that no finite cohort order pins down

This module builds the explicit nonclosure family of NOTE2 §4.1. The architecture law
`thetaLaw θ` of NOTE2 (12) is the four-point law on a binary score and a binary outcome with
masses `1/2`, `(1−θ)/2`, `θ/2`, `0`; its population squared correlation is exactly
`θ/(2−θ)`, which is NOTE2 (13). Every cell mass is affine in `θ`, so the mass of any
size-`n` cohort cell of the independent product law is the evaluation at `θ` of a polynomial
of degree at most `n`. Consequently the two moment-matched parity laws of
`MomentOrderObstruction` — the positive and negative parts of the order-`n+1` alternating
binomial weights, carried by the arithmetic progression `1/4, 1/4 + h, …, 3/4` with
`h = 1/(2(n+1))` — assign *identical* probabilities to every size-`n` cohort outcome while
assigning different expected population squared correlations.

The gap is computed exactly, not merely shown nonzero. Writing `θ/(2−θ) = 2/(2−θ) − 1`
reduces it to the `(n+1)`-st forward difference of a reciprocal, and `fwdDiff_iter_reciprocal`
below proves the closed form `Δ^k_h[x ↦ 1/(c−x)](a) = k! h^k / ∏_{j≤k}(c−a−jh)` by induction
on `k`. The resulting value is NOTE2 (14) with `k = n+1`, `a = 1/4`; it is nonzero because
every denominator on the progression is at least `5/4`. For `n = 1` the two expected squared
correlations are computed to be `13/35` and `1/3`, matching the note.

The last section records the sign-mixture remark of NOTE2 §4.1: the pooled law of two
studies whose population squared correlations are both one is their equal mixture, and its
squared correlation is zero. It reuses `SquaredCorrelationZeroTest.signPairLaw` rather than
rebuilding a four-point law.

Scope. The mixing laws here are finitely supported on an arithmetic progression, which is
what the nonclosure argument needs; general mixing measures on `[1/4, 3/4]` are not treated.
The cohort statement is about the cell masses of `FiniteGeneticTransition.piLaw`, i.e. about
conditionally independent replica draws, exactly as in NOTE2 (11); non-independent evaluation
cohorts are out of scope. The alternating-weight machinery is imported, not reproved.

## Empirical status

None. The bodies here are algebra: `thetaLaw` is a stipulated four-point probability vector
and every quantity below is a polynomial or rational function of its parameter, so no
measurement bears on any statement in this module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ThetaFamilyNonclosure

open Foundations fwdDiff MomentOrderObstruction

noncomputable section

/-! ### The one-parameter architecture family (12) -/

/-- The four masses of NOTE2 (12) on a pair `(score, outcome)` of binary values: the score
is zero with probability one half, and given a positive score the outcome is one with
probability `θ`. -/
def thetaMass (θ : ℝ) : Bool × Bool → ℝ
  | (false, false) => 1 / 2
  | (false, true) => 0
  | (true, false) => (1 - θ) / 2
  | (true, true) => θ / 2

/-- The four masses are nonnegative exactly on the parameter interval of NOTE2 (12). -/
theorem thetaMass_nonneg (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (cell : Bool × Bool) :
    0 ≤ thetaMass θ cell := by
  rcases cell with ⟨s, y⟩
  cases s <;> cases y <;> simp only [thetaMass] <;> linarith

/-- The four masses of NOTE2 (12) sum to one for every parameter value. -/
theorem thetaMass_sum (θ : ℝ) : ∑ cell : Bool × Bool, thetaMass θ cell = 1 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, thetaMass]
  ring

/-- The architecture law of NOTE2 (12) as a finite report law on score and outcome. -/
def thetaLaw (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : FiniteReportLaw (Bool × Bool) where
  mass := thetaMass θ
  mass_nonneg := thetaMass_nonneg θ h0 h1
  mass_sum := thetaMass_sum θ

/-- The same law as a positive normalized expectation functional, which is the form the
corpus variance and covariance take. -/
def thetaExp (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : ExpFunctional (Bool × Bool) :=
  weightedExp (thetaMass θ) (thetaMass_nonneg θ h0 h1) (thetaMass_sum θ)

/-- The law of NOTE2 (12) and its expectation functional carry the same masses. -/
theorem thetaLaw_mass (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (cell : Bool × Bool) :
    (thetaLaw θ h0 h1).mass cell = thetaMass θ cell := rfl

/-- The binary score read as a real number. -/
def scoreValue : Bool × Bool → ℝ
  | (false, _) => 0
  | (true, _) => 1

/-- The binary outcome read as a real number. -/
def outcomeValue : Bool × Bool → ℝ
  | (_, false) => 0
  | (_, true) => 1

/-- Exact evaluation of the architecture law on an arbitrary statistic. -/
theorem thetaExp_apply (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (statistic : Bool × Bool → ℝ) :
    thetaExp θ h0 h1 statistic =
      statistic (false, false) / 2 + (1 - θ) / 2 * statistic (true, false) +
        θ / 2 * statistic (true, true) := by
  simp only [thetaExp, weightedExp_apply, Fintype.sum_prod_type, Fintype.sum_bool, thetaMass]
  ring

/-- The score has mean one half, independently of the parameter. -/
theorem thetaExp_mean_score (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    thetaExp θ h0 h1 scoreValue = 1 / 2 := by
  rw [thetaExp_apply]
  simp only [scoreValue]
  ring

/-- The outcome has mean `θ/2`. -/
theorem thetaExp_mean_outcome (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    thetaExp θ h0 h1 outcomeValue = θ / 2 := by
  rw [thetaExp_apply]
  simp only [outcomeValue]
  ring

/-- The score has variance one quarter. -/
theorem thetaExp_variance_score (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    variance (thetaExp θ h0 h1) scoreValue = 1 / 4 := by
  rw [variance, thetaExp_mean_score, thetaExp_apply]
  simp only [scoreValue]
  ring

/-- The outcome has variance `θ(2−θ)/4`. -/
theorem thetaExp_variance_outcome (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    variance (thetaExp θ h0 h1) outcomeValue = θ * (2 - θ) / 4 := by
  rw [variance, thetaExp_mean_outcome, thetaExp_apply]
  simp only [outcomeValue]
  ring

/-- Score and outcome have covariance `θ/4`. -/
theorem thetaExp_covariance (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    covariance (thetaExp θ h0 h1) scoreValue outcomeValue = θ / 4 := by
  rw [covariance, thetaExp_mean_score, thetaExp_mean_outcome, thetaExp_apply]
  simp only [scoreValue, outcomeValue]
  ring

/-- **NOTE2 (13).** The population squared correlation of the family of NOTE2 (12) is
exactly `θ/(2−θ)`. The premise `0 < θ` is the note's domain condition: it is what makes the
outcome variance, hence the quotient, nonzero. -/
theorem thetaExp_squared_correlation (θ : ℝ) (h0 : 0 < θ) (h1 : θ ≤ 1) :
    covariance (thetaExp θ h0.le h1) scoreValue outcomeValue ^ 2 /
        (variance (thetaExp θ h0.le h1) scoreValue *
          variance (thetaExp θ h0.le h1) outcomeValue) = θ / (2 - θ) := by
  rw [thetaExp_covariance, thetaExp_variance_score, thetaExp_variance_outcome]
  have hne : θ ≠ 0 := ne_of_gt h0
  have h2 : (2 : ℝ) - θ ≠ 0 := by intro hc; linarith
  field_simp

/-- The population squared correlation of NOTE2 (13) as a function of the parameter. -/
def thetaReport (θ : ℝ) : ℝ := θ / (2 - θ)

/-! ### Every cohort cell mass is a polynomial of degree at most the cohort size -/

/-- The affine polynomial whose evaluation at `θ` is the mass of one cell of NOTE2 (12). -/
def thetaCellPoly : Bool × Bool → Polynomial ℝ
  | (false, false) => Polynomial.C (1 / 2)
  | (false, true) => 0
  | (true, false) => Polynomial.C (1 / 2) - Polynomial.C (1 / 2) * Polynomial.X
  | (true, true) => Polynomial.C (1 / 2) * Polynomial.X

/-- Each cell polynomial evaluates to the corresponding mass of NOTE2 (12). -/
theorem thetaCellPoly_eval (θ : ℝ) (cell : Bool × Bool) :
    (thetaCellPoly cell).eval θ = thetaMass θ cell := by
  rcases cell with ⟨s, y⟩
  cases s <;> cases y <;>
    simp only [thetaCellPoly, thetaMass, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_zero] <;> ring

/-- Each cell polynomial is affine, which is the sense in which NOTE2 (12) is affine in its
parameter. -/
theorem thetaCellPoly_natDegree_le (cell : Bool × Bool) :
    (thetaCellPoly cell).natDegree ≤ 1 := by
  have hlin : ((Polynomial.C (1 / 2 : ℝ)) * Polynomial.X).natDegree ≤ 1 := by
    refine Polynomial.natDegree_mul_le.trans ?_
    simp
  rcases cell with ⟨s, y⟩
  cases s <;> cases y <;> simp only [thetaCellPoly]
  · simp
  · simp
  · exact (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) hlin)
  · exact hlin

/-- The mass that the size-`n` independent cohort law assigns to one cohort outcome. -/
def cohortMass (θ : ℝ) {n : ℕ} (outcome : Fin n → Bool × Bool) : ℝ :=
  ∏ i, thetaMass θ (outcome i)

/-- The polynomial in the parameter whose evaluation is that cohort cell mass. -/
def cohortPoly {n : ℕ} (outcome : Fin n → Bool × Bool) : Polynomial ℝ :=
  ∏ i, thetaCellPoly (outcome i)

/-- The cohort cell mass is the evaluation of the cohort polynomial. -/
theorem cohortPoly_eval (θ : ℝ) {n : ℕ} (outcome : Fin n → Bool × Bool) :
    (cohortPoly outcome).eval θ = cohortMass θ outcome := by
  simp only [cohortPoly, cohortMass, Polynomial.eval_prod]
  exact Finset.prod_congr rfl fun i _ ↦ thetaCellPoly_eval θ (outcome i)

/-- **The degree bound behind the nonclosure family.** The mass of a size-`n` cohort cell is
a polynomial of degree at most `n` in the architecture parameter. -/
theorem cohortPoly_natDegree_le {n : ℕ} (outcome : Fin n → Bool × Bool) :
    (cohortPoly outcome).natDegree ≤ n := by
  refine (Polynomial.natDegree_prod_le Finset.univ fun i ↦ thetaCellPoly (outcome i)).trans ?_
  calc ∑ i : Fin n, (thetaCellPoly (outcome i)).natDegree
      ≤ ∑ _i : Fin n, 1 :=
        Finset.sum_le_sum fun i _ ↦ thetaCellPoly_natDegree_le (outcome i)
    _ = n := by simp

/-- The cohort cell mass is exactly the mass that the corpus independent product law
assigns, so the polynomial statement above is a statement about `piLaw`. -/
theorem cohortMass_eq_piLaw_mass (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {n : ℕ}
    (outcome : Fin n → Bool × Bool) :
    cohortMass θ outcome =
      (FiniteGeneticTransition.piLaw fun _ : Fin n ↦ thetaLaw θ h0 h1).mass outcome :=
  (FiniteGeneticTransition.piLaw_mass (fun _ : Fin n ↦ thetaLaw θ h0 h1) outcome).symm

/-- **NOTE2 §4.1, cohort indistinguishability.** The two moment-matched parity laws of
`MomentOrderObstruction` assign the same probability to every size-`n` cohort outcome, for
every arithmetic progression of architecture parameters. -/
theorem cohort_mass_moments_match (n : ℕ) (a step : ℝ) (outcome : Fin n → Bool × Bool) :
    parityExp n false (fun j ↦ cohortMass (a + (j : ℕ) * step) outcome) =
      parityExp n true (fun j ↦ cohortMass (a + (j : ℕ) * step) outcome) := by
  have h := parity_moment_match n a step (cohortPoly outcome)
    (cohortPoly_natDegree_le outcome)
  simpa only [cohortPoly_eval] using h

/-! ### The closed form of the iterated forward difference of a reciprocal -/

/-- The product of the `k+1` denominators met by an order-`k` forward difference of the
reciprocal `x ↦ 1/(c − x)` started at `a` with step `step`. -/
def nodeProduct (c a step : ℝ) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range (k + 1), (c - a - (j : ℝ) * step)

/-- Splitting the last factor off the denominator product. -/
theorem nodeProduct_succ (c a step : ℝ) (k : ℕ) :
    nodeProduct c a step (k + 1) =
      nodeProduct c a step k * (c - a - ((k : ℝ) + 1) * step) := by
  simp only [nodeProduct]
  rw [Finset.prod_range_succ]
  push_cast
  ring

/-- Shifting the base point by one step drops the first factor of the denominator
product. -/
theorem nodeProduct_shift (c a step : ℝ) (k : ℕ) :
    nodeProduct c a step (k + 1) = (c - a) * nodeProduct c (a + step) step k := by
  simp only [nodeProduct]
  rw [Finset.prod_range_succ' (fun j ↦ c - a - (j : ℝ) * step) (k + 1)]
  rw [mul_comm]
  congr 1
  · norm_num
  · exact Finset.prod_congr rfl fun j _ ↦ by push_cast; ring

/-- Nonvanishing of every factor makes the denominator product nonzero. -/
theorem nodeProduct_ne_zero (c a step : ℝ) (k : ℕ)
    (hne : ∀ j ∈ Finset.range (k + 1), c - a - (j : ℝ) * step ≠ 0) :
    nodeProduct c a step k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr hne

/-- **The finite-difference gap formula for a reciprocal.** For every order `k`, base point
`a` and step, provided no denominator on the progression vanishes,
`Δ^k_h[x ↦ 1/(c−x)](a) = k! h^k / ∏_{j=0}^{k}(c − a − jh)`. This is the identity NOTE2 §4.1
uses to evaluate the nonclosure gap (14); it is proved here by induction on `k`. -/
theorem fwdDiff_iter_reciprocal (c step : ℝ) :
    ∀ (k : ℕ) (a : ℝ), (∀ j ∈ Finset.range (k + 1), c - a - (j : ℝ) * step ≠ 0) →
      Δ_[step]^[k] (fun x ↦ 1 / (c - x)) a =
        (Nat.factorial k : ℝ) * step ^ k / nodeProduct c a step k := by
  intro k
  induction k with
  | zero =>
    intro a _
    simp [nodeProduct]
  | succ k ih =>
    intro a hne
    have hmemA : ∀ j ∈ Finset.range (k + 1), c - a - (j : ℝ) * step ≠ 0 := by
      intro j hj
      exact hne j (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hj)))
    have hmemB : ∀ j ∈ Finset.range (k + 1), c - (a + step) - (j : ℝ) * step ≠ 0 := by
      intro j hj
      have hj' : j + 1 ∈ Finset.range (k + 2) :=
        Finset.mem_range.mpr (Nat.succ_lt_succ (Finset.mem_range.mp hj))
      have h := hne (j + 1) hj'
      intro hc
      apply h
      push_cast
      linarith
    have hca : c - a ≠ 0 := by
      have h := hne 0 (Finset.mem_range.mpr (Nat.succ_pos _))
      simpa using h
    have hlast : c - a - ((k : ℝ) + 1) * step ≠ 0 := by
      have h := hne (k + 1) (Finset.mem_range.mpr (Nat.lt_succ_self _))
      push_cast at h
      exact h
    set B : ℝ := nodeProduct c a step k with hBdef
    set A : ℝ := nodeProduct c (a + step) step k with hAdef
    have hBne : B ≠ 0 := nodeProduct_ne_zero c a step k hmemA
    have hAne : A ≠ 0 := nodeProduct_ne_zero c (a + step) step k hmemB
    have hstep : Δ_[step]^[k + 1] (fun x ↦ 1 / (c - x)) a =
        Δ_[step]^[k] (fun x ↦ 1 / (c - x)) (a + step) -
          Δ_[step]^[k] (fun x ↦ 1 / (c - x)) a := by
      rw [Function.iterate_succ_apply']
      rfl
    rw [hstep, ih (a + step) hmemB, ih a hmemA, ← hAdef, ← hBdef]
    have hR1 : nodeProduct c a step (k + 1) = (c - a) * A := nodeProduct_shift c a step k
    have hR2 : nodeProduct c a step (k + 1) = B * (c - a - ((k : ℝ) + 1) * step) :=
      nodeProduct_succ c a step k
    have hA' : A = nodeProduct c a step (k + 1) / (c - a) := by
      rw [hR1, mul_comm, mul_div_assoc, div_self hca, mul_one]
    have hB' : B = nodeProduct c a step (k + 1) / (c - a - ((k : ℝ) + 1) * step) := by
      rw [hR2, mul_div_assoc, div_self hlast, mul_one]
    rw [hA', hB', div_div_eq_mul_div, div_div_eq_mul_div, div_sub_div_same]
    have hnum : (Nat.factorial k : ℝ) * step ^ k * (c - a) -
        (Nat.factorial k : ℝ) * step ^ k * (c - a - ((k : ℝ) + 1) * step) =
          (Nat.factorial (k + 1) : ℝ) * step ^ (k + 1) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hnum]

/-! ### The exact nonclosure gap (14) -/

/-- The base point of the progression of NOTE2 §4.1. -/
def nodeBase : ℝ := 1 / 4

/-- The step of the progression of NOTE2 §4.1 for a cohort of size `n`. -/
def nodeStep (n : ℕ) : ℝ := 1 / (2 * ((n : ℝ) + 1))

/-- The step is positive. -/
theorem nodeStep_pos (n : ℕ) : 0 < nodeStep n := by
  unfold nodeStep
  positivity

/-- Every node of the progression lies in the parameter window `[1/4, 3/4]` of NOTE2 (12),
so each of them is a legitimate architecture parameter. -/
theorem node_mem_window (n j : ℕ) (hj : j ∈ Finset.range (n + 2)) :
    1 / 4 ≤ nodeBase + (j : ℝ) * nodeStep n ∧
      nodeBase + (j : ℝ) * nodeStep n ≤ 3 / 4 := by
  have hjle : (j : ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact_mod_cast this
  have hpos : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
  have hupper : (j : ℝ) * nodeStep n ≤ ((n : ℝ) + 1) * nodeStep n :=
    mul_le_mul_of_nonneg_right hjle (nodeStep_pos n).le
  have heq : ((n : ℝ) + 1) * nodeStep n = 1 / 2 := by
    unfold nodeStep
    field_simp
  have hnonneg : (0 : ℝ) ≤ (j : ℝ) * nodeStep n :=
    mul_nonneg (Nat.cast_nonneg j) (nodeStep_pos n).le
  rw [heq] at hupper
  unfold nodeBase
  constructor <;> linarith

/-- Every denominator met on the progression is bounded below by `5/4`, which is what makes
the nonclosure gap of NOTE2 (14) finite and nonzero. -/
theorem node_denominator_pos (n j : ℕ) (hj : j ∈ Finset.range (n + 2)) :
    0 < 2 - nodeBase - (j : ℝ) * nodeStep n := by
  have h := (node_mem_window n j hj).2
  unfold nodeBase at h ⊢
  linarith

/-- The alternating binomial sum of the population squared correlation is twice that of the
reciprocal, because the constant part of `θ/(2−θ) = 2/(2−θ) − 1` is annihilated. -/
theorem alternating_thetaReport_sum (n : ℕ) (a step : ℝ)
    (hne : ∀ j ∈ Finset.range (n + 2), (2 : ℝ) - a - (j : ℝ) * step ≠ 0) :
    ∑ j ∈ Finset.range (n + 2),
        (-1 : ℝ) ^ j * ((n + 1).choose j : ℝ) * thetaReport (a + (j : ℝ) * step) =
      2 * ∑ j ∈ Finset.range (n + 2),
        (-1 : ℝ) ^ j * ((n + 1).choose j : ℝ) * (1 / (2 - (a + (j : ℝ) * step))) := by
  have hconst : ∑ j ∈ Finset.range (n + 2),
      (-1 : ℝ) ^ j * ((n + 1).choose j : ℝ) * (1 : ℝ) = 0 := by
    have h := alternating_annihilates n a step 1 (by simp)
    simpa using h
  have hpoint : ∀ j ∈ Finset.range (n + 2),
      (-1 : ℝ) ^ j * ((n + 1).choose j : ℝ) * thetaReport (a + (j : ℝ) * step) =
        2 * ((-1 : ℝ) ^ j * ((n + 1).choose j : ℝ) * (1 / (2 - (a + (j : ℝ) * step)))) -
          (-1 : ℝ) ^ j * ((n + 1).choose j : ℝ) * (1 : ℝ) := by
    intro j hj
    have hd : (2 : ℝ) - (a + (j : ℝ) * step) ≠ 0 := by
      have h := hne j hj
      intro hc
      apply h
      linarith
    unfold thetaReport
    field_simp
    ring
  rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib, ← Finset.mul_sum, hconst,
    sub_zero]

/-- **NOTE2 (14).** The exact gap between the two moment-matched parity laws in expected
population squared correlation, for any progression on which no denominator vanishes. With
`k = n+1` this is the note's `Δ_n = (−1)^k 2 k! h^k / (2^{k−1} ∏_{j=0}^{k}(2 − a − jh))`. -/
theorem parity_thetaReport_gap (n : ℕ) (a step : ℝ)
    (hne : ∀ j ∈ Finset.range (n + 2), (2 : ℝ) - a - (j : ℝ) * step ≠ 0) :
    parityExp n false (fun j ↦ thetaReport (a + (j : ℕ) * step)) -
        parityExp n true (fun j ↦ thetaReport (a + (j : ℕ) * step)) =
      2 * (-1 : ℝ) ^ (n + 1) * (Nat.factorial (n + 1) : ℝ) * step ^ (n + 1) /
        (2 ^ n * nodeProduct 2 a step (n + 1)) := by
  have hgap := parity_gap n a step thetaReport
  have halt := alternating_thetaReport_sum n a step hne
  have hfd := fwdDiff_iter_eq_alternating n a step (fun x ↦ 1 / (2 - x))
  have hrec := fwdDiff_iter_reciprocal 2 step (n + 1) a hne
  have hsq : ((-1 : ℝ) ^ (n + 1)) * ((-1 : ℝ) ^ (n + 1)) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨n + 1, rfl⟩
  have hmul := congrArg (fun t : ℝ ↦ (-1 : ℝ) ^ (n + 1) * t) hfd
  simp only at hmul
  rw [← mul_assoc, hsq, one_mul] at hmul
  have hS : ∑ j ∈ Finset.range (n + 2),
      (-1 : ℝ) ^ j * ((n + 1).choose j : ℝ) * (1 / (2 - (a + (j : ℝ) * step))) =
        (-1 : ℝ) ^ (n + 1) *
          ((Nat.factorial (n + 1) : ℝ) * step ^ (n + 1) / nodeProduct 2 a step (n + 1)) := by
    rw [← hrec, ← hmul]
  rw [hgap, halt, hS]
  ring

/-- **NOTE2 §4.1, nonclosure at every order.** On the progression of NOTE2 §4.1 the two
parity laws report different expected population squared correlations, at every cohort
size `n`, even though by `cohort_mass_moments_match` they induce the very same size-`n`
cohort law. -/
theorem parity_thetaReport_gap_ne_zero (n : ℕ) :
    parityExp n false (fun j ↦ thetaReport (nodeBase + (j : ℕ) * nodeStep n)) ≠
      parityExp n true (fun j ↦ thetaReport (nodeBase + (j : ℕ) * nodeStep n)) := by
  intro heq
  have hne : ∀ j ∈ Finset.range (n + 2),
      (2 : ℝ) - nodeBase - (j : ℝ) * nodeStep n ≠ 0 := fun j hj ↦
    (node_denominator_pos n j hj).ne'
  have hgap := parity_thetaReport_gap n nodeBase (nodeStep n) hne
  rw [heq, sub_self] at hgap
  have hprod : 0 < nodeProduct 2 nodeBase (nodeStep n) (n + 1) :=
    Finset.prod_pos fun j hj ↦ node_denominator_pos n j hj
  have hnum : 2 * (-1 : ℝ) ^ (n + 1) * (Nat.factorial (n + 1) : ℝ) *
      nodeStep n ^ (n + 1) ≠ 0 := by
    have h1 : ((-1 : ℝ) ^ (n + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h2 : (Nat.factorial (n + 1) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h3 : nodeStep n ^ (n + 1) ≠ 0 := pow_ne_zero _ (nodeStep_pos n).ne'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero h1) h2) h3
  have hden : (2 : ℝ) ^ n * nodeProduct 2 nodeBase (nodeStep n) (n + 1) ≠ 0 := by
    have : (0 : ℝ) < 2 ^ n * nodeProduct 2 nodeBase (nodeStep n) (n + 1) := by positivity
    exact this.ne'
  exact (div_ne_zero hnum hden) hgap.symm

/-- **NOTE2 §4.1 at `n = 1`.** The two architecture laws with identical one-person report
laws report expected population squared correlations `13/35` and `1/3`. -/
theorem parity_thetaReport_values_one :
    parityExp 1 false (fun j ↦ thetaReport (nodeBase + (j : ℕ) * nodeStep 1)) = 13 / 35 ∧
      parityExp 1 true (fun j ↦ thetaReport (nodeBase + (j : ℕ) * nodeStep 1)) = 1 / 3 := by
  have hstep : nodeStep 1 = 1 / 4 := by norm_num [nodeStep]
  have w0 : alternatingWeight 1 0 = 1 / 2 := by norm_num [alternatingWeight]
  have w1 : alternatingWeight 1 1 = -1 := by norm_num [alternatingWeight]
  have w2 : alternatingWeight 1 2 = 1 / 2 := by norm_num [alternatingWeight]
  have a0 : |(1 / 2 : ℝ)| = 1 / 2 := abs_of_nonneg (by norm_num)
  have a1 : |(-1 : ℝ)| = 1 := by rw [abs_neg, abs_one]
  have hv0 : thetaReport (nodeBase + (0 : ℝ) * nodeStep 1) = 1 / 7 := by
    norm_num [thetaReport, nodeBase, hstep]
  have hv1 : thetaReport (nodeBase + (1 : ℝ) * nodeStep 1) = 1 / 3 := by
    norm_num [thetaReport, nodeBase, hstep]
  have hv2 : thetaReport (nodeBase + (2 : ℝ) * nodeStep 1) = 3 / 5 := by
    norm_num [thetaReport, nodeBase, hstep]
  have key : ∀ s : Bool,
      parityExp 1 s (fun j ↦ thetaReport (nodeBase + (j : ℕ) * nodeStep 1)) =
        parityMass 1 s 0 * thetaReport (nodeBase + (0 : ℝ) * nodeStep 1) +
          parityMass 1 s 1 * thetaReport (nodeBase + (1 : ℝ) * nodeStep 1) +
          parityMass 1 s 2 * thetaReport (nodeBase + (2 : ℝ) * nodeStep 1) := by
    intro s
    simp only [parityExp, weightedExp_apply]
    rw [Fin.sum_univ_eq_sum_range
      (fun j ↦ parityMass 1 s j * thetaReport (nodeBase + (j : ℝ) * nodeStep 1)) 3,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    norm_num
  refine ⟨?_, ?_⟩
  · rw [key false, hv0, hv1, hv2]
    norm_num [parityMass, w0, w1, w2, a0, a1]
  · rw [key true, hv0, hv1, hv2]
    norm_num [parityMass, w0, w1, w2, a0, a1]

/-- The `n = 1` gap of NOTE2 §4.1 is exactly `4/105`. -/
theorem parity_thetaReport_gap_one :
    parityExp 1 false (fun j ↦ thetaReport (nodeBase + (j : ℕ) * nodeStep 1)) -
        parityExp 1 true (fun j ↦ thetaReport (nodeBase + (j : ℕ) * nodeStep 1)) =
      4 / 105 := by
  rw [parity_thetaReport_values_one.1, parity_thetaReport_values_one.2]
  norm_num

/-- **NOTE2 §4.1, the nonclosure statement in one place.** At every cohort size `n` the two
parity laws on the progression `1/4, 1/4 + h, …, 3/4` induce identical size-`n` cohort laws
and different expected population squared correlations. No finite cohort order identifies the
expected report. -/
theorem parity_cohorts_match_reports_differ (n : ℕ) :
    (∀ outcome : Fin n → Bool × Bool,
        parityExp n false
            (fun j ↦ cohortMass (nodeBase + (j : ℕ) * nodeStep n) outcome) =
          parityExp n true
            (fun j ↦ cohortMass (nodeBase + (j : ℕ) * nodeStep n) outcome)) ∧
      parityExp n false (fun j ↦ thetaReport (nodeBase + (j : ℕ) * nodeStep n)) ≠
        parityExp n true (fun j ↦ thetaReport (nodeBase + (j : ℕ) * nodeStep n)) :=
  ⟨fun outcome ↦ cohort_mass_moments_match n nodeBase (nodeStep n) outcome,
    parity_thetaReport_gap_ne_zero n⟩

/-! ### The sign-mixture example -/

/-- **NOTE2 §4.1, sign mixture.** The pooled law of the two sign studies is their equal
mixture: on every statistic the uncorrelated four-point law is the average of the perfectly
positively and the perfectly negatively correlated ones. -/
theorem signPair_pooled_is_average (statistic : Bool × Bool → ℝ) :
    SquaredCorrelationZeroTest.signPairLaw 0 (by norm_num [abs_le]) statistic =
      (SquaredCorrelationZeroTest.signPairLaw 1 (by norm_num [abs_le]) statistic +
        SquaredCorrelationZeroTest.signPairLaw (-1) (by norm_num [abs_le]) statistic) / 2 := by
  rw [SquaredCorrelationZeroTest.signPairLaw_apply,
    SquaredCorrelationZeroTest.signPairLaw_apply,
    SquaredCorrelationZeroTest.signPairLaw_apply]
  ring

/-- The population squared correlation of a sign-pair study with prescribed correlation. -/
def signReport (corr : ℝ) (hcorr : |corr| ≤ 1) : ℝ :=
  covariance (SquaredCorrelationZeroTest.signPairLaw corr hcorr)
      SquaredCorrelationZeroTest.scoreVar SquaredCorrelationZeroTest.outcomeVar ^ 2 /
    (variance (SquaredCorrelationZeroTest.signPairLaw corr hcorr)
        SquaredCorrelationZeroTest.scoreVar *
      variance (SquaredCorrelationZeroTest.signPairLaw corr hcorr)
        SquaredCorrelationZeroTest.outcomeVar)

/-- **NOTE2 §4.1, sign mixture, reports.** Each of the two studies has population squared
correlation one while the pooled law of `signPair_pooled_is_average` has population squared
correlation zero. -/
theorem signReport_pooled_values :
    signReport 1 (by norm_num [abs_le]) = 1 ∧ signReport (-1) (by norm_num [abs_le]) = 1 ∧
      signReport 0 (by norm_num [abs_le]) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [signReport,
      SquaredCorrelationZeroTest.signPairLaw_squared_correlation] <;> norm_num

end

end Descent.Portability.ThetaFamilyNonclosure
