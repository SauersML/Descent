/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ApproximationDuality
import Mathlib.LinearAlgebra.Lagrange

assert_below Descent.Decision Descent.Program

/-!
# Radial interpolation and maximal ambiguity at every finite raw-moment order

PL Lemma 7.1 and Theorem 7.2. The Lagrange weights of interpolation at `k+1` distinct
positive radii, evaluated at the origin, sum to one and annihilate every positive power
up to `k`. Splitting those weights by sign across two rays produces two finitely
supported outcome laws with identical joint raw moments of every total degree at most
`k` whose expected scale-invariant report differs by exactly `(F u - F v)` divided by
the total variation of the weights. The hypotheses are the manuscript's domain
conditions: distinct positive radii, positive scaling invariance of the report, and a
multi-index of total degree at most `k`.

Corollary 7.3's expectation form and Corollary 7.5's recovery bound follow, the latter
through `ApproximationDuality.recovery_error_lower`. The laws are
`Portability.weightedExp` probability vectors on `Fin (k+1) × Bool`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.RadialInterpolation

open Foundations

noncomputable section

variable {k : ℕ} {N : Type*} [Fintype N]

/-- The Lagrange weight of the radius `r i`, evaluated at the origin: PL equation
(7.1). -/
def radialWeight (r : Fin (k + 1) → ℝ) (i : Fin (k + 1)) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, (-(r j)) / (r i - r j)

/-- The radial weight is the Lagrange basis polynomial evaluated at zero. -/
theorem radialWeight_eq_eval_basis (r : Fin (k + 1) → ℝ) (i : Fin (k + 1)) :
    (Lagrange.basis Finset.univ r i).eval 0 = radialWeight r i := by
  simp only [Lagrange.basis, Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  simp [Lagrange.basisDivisor, div_eq_inv_mul]

/-- **PL Lemma 7.1, interpolation identity.** The radial weights reconstruct the value
at the origin of every polynomial of degree at most `k`. -/
theorem radial_interpolation (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r)
    (p : Polynomial ℝ) (hdeg : p.degree < (k + 1 : ℕ)) :
    ∑ i, radialWeight r i * p.eval (r i) = p.eval 0 := by
  have hcard : (Finset.univ : Finset (Fin (k + 1))).card = k + 1 := by simp
  have hvs : Set.InjOn r (Finset.univ : Finset (Fin (k + 1))) := fun a _ b _ h ↦ hinj h
  have hrep := Lagrange.eq_interpolate (v := r) hvs (f := p) (by rwa [hcard])
  conv_rhs => rw [hrep]
  rw [Lagrange.interpolate_apply, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, radialWeight_eq_eval_basis]
  ring

/-- **PL Lemma 7.1, first identity.** The radial weights sum to one. -/
theorem radialWeight_sum (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r) :
    ∑ i, radialWeight r i = 1 := by
  have h := radial_interpolation r hinj 1
    (by rw [Polynomial.degree_one]; exact_mod_cast Nat.succ_pos k)
  simpa using h

/-- **PL Lemma 7.1, second identity.** The radial weights annihilate every positive
power up to `k`. -/
theorem radialWeight_moment (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r)
    {m : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k) :
    ∑ i, radialWeight r i * r i ^ m = 0 := by
  have hdeg : (Polynomial.X ^ m : Polynomial ℝ).degree < (k + 1 : ℕ) := by
    rw [Polynomial.degree_X_pow]
    exact_mod_cast Nat.lt_succ_of_le hmk
  have h := radial_interpolation r hinj (Polynomial.X ^ m) hdeg
  simpa [zero_pow (by omega : m ≠ 0)] using h

/-- The total variation of the radial weights: `c_ε` of PL equation (7.2). -/
def radialTotal (r : Fin (k + 1) → ℝ) : ℝ := ∑ i, |radialWeight r i|

/-- The total variation of the radial weights is at least one. -/
theorem one_le_radialTotal (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r) :
    1 ≤ radialTotal r := by
  rw [← radialWeight_sum r hinj]
  exact Finset.sum_le_sum fun i _ ↦ le_abs_self _

/-- The weight attached to the smallest radius is positive: the `w₀ > 0` half of
PL Lemma 7.1. -/
theorem radialWeight_pos_of_min (r : Fin (k + 1) → ℝ) (hpos : ∀ j, 0 < r j)
    (i : Fin (k + 1)) (hlt : ∀ j, j ≠ i → r i < r j) : 0 < radialWeight r i := by
  refine Finset.prod_pos fun j hj ↦ ?_
  have hne : j ≠ i := Finset.ne_of_mem_erase hj
  have hij := hlt j hne
  have heq : (-(r j)) / (r i - r j) = r j / (r j - r i) := by
    rw [show r i - r j = -(r j - r i) by ring, neg_div_neg_eq]
  rw [heq]
  exact div_pos (hpos j) (by linarith)

/-- The sign-split masses of the radial weights: the positive part goes to one ray and
the negative part to the other. -/
def radialMass (r : Fin (k + 1) → ℝ) (z : Fin (k + 1) × Bool) : ℝ :=
  if z.2 then (|radialWeight r z.1| + radialWeight r z.1) / 2
  else (|radialWeight r z.1| - radialWeight r z.1) / 2

/-- The two moment-matched laws: `s = false` is `P_ε`, `s = true` is `Q_ε`, obtained by
exchanging the two rays. -/
def radialLaw (r : Fin (k + 1) → ℝ) (s : Bool) (z : Fin (k + 1) × Bool) : ℝ :=
  radialMass r (z.1, xor s z.2) / radialTotal r

/-- Every support point carries nonnegative mass. -/
theorem radialLaw_nonneg (r : Fin (k + 1) → ℝ) (s : Bool) (z : Fin (k + 1) × Bool) :
    0 ≤ radialLaw r s z := by
  have hT : 0 ≤ radialTotal r := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  refine div_nonneg ?_ hT
  unfold radialMass
  split
  · linarith [neg_abs_le (radialWeight r z.1)]
  · linarith [le_abs_self (radialWeight r z.1)]

/-- Both laws are probability laws. -/
theorem radialLaw_sum (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r) (s : Bool) :
    ∑ z, radialLaw r s z = 1 := by
  have hT : (0 : ℝ) < radialTotal r := lt_of_lt_of_le one_pos (one_le_radialTotal r hinj)
  have hmass : ∑ z : Fin (k + 1) × Bool, radialMass r (z.1, xor s z.2) =
      radialTotal r := by
    simp only [radialTotal]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    cases s <;> simp [radialMass] <;> ring
  simp only [radialLaw]
  rw [← Finset.sum_div, hmass, div_self hT.ne']

/-- The two support rays: the template `u` carries the positive part of each weight
under `P_ε` and the negative part under `Q_ε`. -/
def radialPoint (r : Fin (k + 1) → ℝ) (u v : N → ℝ) (z : Fin (k + 1) × Bool) : N → ℝ :=
  if z.2 then r z.1 • u else r z.1 • v

/-- The two moment-matched expectations of PL equation (7.5). -/
def radialExp (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r) (s : Bool) :
    ExpFunctional (Fin (k + 1) × Bool) :=
  weightedExp (radialLaw r s) (radialLaw_nonneg r s) (radialLaw_sum r hinj s)

/-- **The master gap identity.** For any observable of the outcome vector, the two laws
differ by the radial-weight average of its values on the two rays. -/
theorem radial_gap (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r) (u v : N → ℝ)
    (g : (N → ℝ) → ℝ) :
    radialExp r hinj false (fun z ↦ g (radialPoint r u v z)) -
        radialExp r hinj true (fun z ↦ g (radialPoint r u v z)) =
      (∑ i, radialWeight r i * (g (r i • u) - g (r i • v))) / radialTotal r := by
  simp only [radialExp, weightedExp_apply]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_sub_distrib,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hP0 : radialLaw r false (i, false) =
      (|radialWeight r i| - radialWeight r i) / 2 / radialTotal r := rfl
  have hP1 : radialLaw r false (i, true) =
      (|radialWeight r i| + radialWeight r i) / 2 / radialTotal r := rfl
  have hQ0 : radialLaw r true (i, false) =
      (|radialWeight r i| + radialWeight r i) / 2 / radialTotal r := rfl
  have hQ1 : radialLaw r true (i, true) =
      (|radialWeight r i| - radialWeight r i) / 2 / radialTotal r := rfl
  have hU : radialPoint r u v (i, true) = r i • u := rfl
  have hV : radialPoint r u v (i, false) = r i • v := rfl
  simp only [Fintype.sum_bool, hP0, hP1, hQ0, hQ1, hU, hV]
  ring

/-- The raw monomial of a multi-index. -/
def monomialEval (α : N → ℕ) (y : N → ℝ) : ℝ := ∏ i, y i ^ α i

/-- Raw monomials are homogeneous of their total degree. -/
theorem monomialEval_smul (α : N → ℕ) (t : ℝ) (y : N → ℝ) :
    monomialEval α (t • y) = t ^ (∑ i, α i) * monomialEval α y := by
  unfold monomialEval
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ ↦ by rw [Pi.smul_apply, smul_eq_mul, mul_pow]

/-- **PL Theorem 7.2, moment matching.** The two laws share every joint raw moment of
total degree at most `k`. -/
theorem radial_moment_match (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r)
    (u v : N → ℝ) (α : N → ℕ) (hα : ∑ i, α i ≤ k) :
    radialExp r hinj false (fun z ↦ monomialEval α (radialPoint r u v z)) =
      radialExp r hinj true (fun z ↦ monomialEval α (radialPoint r u v z)) := by
  have hgap := radial_gap r hinj u v (monomialEval α)
  have hzero : ∑ i, radialWeight r i *
      (monomialEval α (r i • u) - monomialEval α (r i • v)) = 0 := by
    have hterm : ∀ i : Fin (k + 1), radialWeight r i *
        (monomialEval α (r i • u) - monomialEval α (r i • v)) =
          (monomialEval α u - monomialEval α v) *
            (radialWeight r i * r i ^ (∑ j, α j)) := by
      intro i
      rw [monomialEval_smul, monomialEval_smul]
      ring
    rw [Finset.sum_congr rfl fun i _ ↦ hterm i, ← Finset.mul_sum]
    rcases Nat.eq_zero_or_pos (∑ j, α j) with h | h
    · have hu : monomialEval α u = 1 := by
        unfold monomialEval
        refine Finset.prod_eq_one fun i _ ↦ ?_
        rw [Finset.sum_eq_zero_iff.mp h i (Finset.mem_univ i), pow_zero]
      have hv : monomialEval α v = 1 := by
        unfold monomialEval
        refine Finset.prod_eq_one fun i _ ↦ ?_
        rw [Finset.sum_eq_zero_iff.mp h i (Finset.mem_univ i), pow_zero]
      rw [hu, hv]
      ring
    · rw [radialWeight_moment r hinj h hα, mul_zero]
  rw [hzero, zero_div] at hgap
  linarith

/-- **PL Theorem 7.2, equation (7.3).** The expected scale-invariant report differs by
exactly the template report gap divided by the total variation of the weights. -/
theorem radial_report_gap (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r)
    (hpos : ∀ i, 0 < r i) (u v : N → ℝ) (F : (N → ℝ) → ℝ)
    (hF : ∀ t : ℝ, 0 < t → ∀ y : N → ℝ, F (t • y) = F y) :
    radialExp r hinj false (fun z ↦ F (radialPoint r u v z)) -
        radialExp r hinj true (fun z ↦ F (radialPoint r u v z)) =
      (F u - F v) / radialTotal r := by
  have hgap := radial_gap r hinj u v F
  have hnum : ∑ i, radialWeight r i * (F (r i • u) - F (r i • v)) = F u - F v := by
    have hterm : ∀ i : Fin (k + 1), radialWeight r i * (F (r i • u) - F (r i • v)) =
        radialWeight r i * (F u - F v) := by
      intro i
      rw [hF (r i) (hpos i) u, hF (r i) (hpos i) v]
    rw [Finset.sum_congr rfl fun i _ ↦ hterm i, ← Finset.sum_mul,
      radialWeight_sum r hinj, one_mul]
  rw [hnum] at hgap
  exact hgap

/-- **PL Corollary 7.3, expectation form.** The same construction hides the whole report
law, not only its mean: every bounded test function of a scale-invariant report has the
same exact gap. This is the expectation statement; the total-variation bound on the
pushforward laws is not proved here. -/
theorem radial_report_law_gap (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r)
    (hpos : ∀ i, 0 < r i) (u v : N → ℝ) (F : (N → ℝ) → ℝ) (φ : ℝ → ℝ)
    (hF : ∀ t : ℝ, 0 < t → ∀ y : N → ℝ, F (t • y) = F y) :
    radialExp r hinj false (fun z ↦ φ (F (radialPoint r u v z))) -
        radialExp r hinj true (fun z ↦ φ (F (radialPoint r u v z))) =
      (φ (F u) - φ (F v)) / radialTotal r :=
  radial_report_gap r hinj hpos u v (fun y ↦ φ (F y))
    fun t ht y ↦ by simp only [hF t ht y]

/-- **PL Corollary 7.5.** A rule that reports a single number from the shared moment
vector errs, on one of the two laws, by at least half the exact report gap. -/
theorem radial_recovery_error (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r)
    (hpos : ∀ i, 0 < r i) (u v : N → ℝ) (F : (N → ℝ) → ℝ)
    (hF : ∀ t : ℝ, 0 < t → ∀ y : N → ℝ, F (t • y) = F y) (θ : ℝ) :
    (F u - F v) / radialTotal r / 2 ≤
      max |radialExp r hinj false (fun z ↦ F (radialPoint r u v z)) - θ|
        |radialExp r hinj true (fun z ↦ F (radialPoint r u v z)) - θ| := by
  have hgap := radial_report_gap r hinj hpos u v F hF
  have hlow := ApproximationDuality.recovery_error_lower
    (f := fun z ↦ F (radialPoint r u v z)) (radialLaw r false) (radialLaw r true) θ
  rw [← hgap]
  exact hlow

end

end Descent.Portability.RadialInterpolation
