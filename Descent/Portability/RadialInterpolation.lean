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

/-- The radial expectations are the corpus' `Portability.weightedExp` expectations of the
sign-split radial masses. -/
theorem radialExp_eq_weightedExp (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r)
    (s : Bool) :
    radialExp r hinj s =
      weightedExp (radialLaw r s) (radialLaw_nonneg r s) (radialLaw_sum r hinj s) := rfl

/-- **The master gap identity, general form.** For any observable of the support point,
the two laws differ by the radial-weight average of its values on the two branches. -/
theorem radial_gap_general (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r)
    (G : Fin (k + 1) × Bool → ℝ) :
    radialExp r hinj false G - radialExp r hinj true G =
      (∑ i, radialWeight r i * (G (i, true) - G (i, false))) / radialTotal r := by
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
  simp only [Fintype.sum_bool, hP0, hP1, hQ0, hQ1]
  ring

/-- **The master gap identity.** For any observable of the outcome vector, the two laws
differ by the radial-weight average of its values on the two rays. -/
theorem radial_gap (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r) (u v : N → ℝ)
    (g : (N → ℝ) → ℝ) :
    radialExp r hinj false (fun z ↦ g (radialPoint r u v z)) -
        radialExp r hinj true (fun z ↦ g (radialPoint r u v z)) =
      (∑ i, radialWeight r i * (g (r i • u) - g (r i • v))) / radialTotal r :=
  radial_gap_general r hinj (fun z ↦ g (radialPoint r u v z))

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

/-- The radius family of PL Lemma 7.1: one small radius `t` and the integers `1,…,k`. -/
def radii (k : ℕ) (t : ℝ) : Fin (k + 1) → ℝ := fun i ↦ if i = 0 then t else ((i : ℕ) : ℝ)

/-- At `t = 0` every radius is its own index. -/
theorem radii_zero (k : ℕ) (i : Fin (k + 1)) : radii k 0 i = ((i : ℕ) : ℝ) := by
  unfold radii
  by_cases hi : i = 0
  · simp [hi]
  · simp [hi]

/-- The radii are distinct for a small positive `t`. -/
theorem radii_injective (k : ℕ) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    Function.Injective (radii k t) := by
  intro i j hij
  unfold radii at hij
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · rw [hi, hj]
  · exfalso
    rw [if_pos hi, if_neg hj] at hij
    have h1 : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.mpr fun hc ↦ hj (Fin.val_eq_zero_iff.mp hc)
    have h2 : (1 : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  · exfalso
    rw [if_neg hi, if_pos hj] at hij
    have h1 : 1 ≤ (i : ℕ) := Nat.one_le_iff_ne_zero.mpr fun hc ↦ hi (Fin.val_eq_zero_iff.mp hc)
    have h2 : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  · rw [if_neg hi, if_neg hj] at hij
    have : (i : ℕ) = (j : ℕ) := by exact_mod_cast hij
    exact Fin.val_injective this

/-- The radii are positive for a positive `t`. -/
theorem radii_pos (k : ℕ) (t : ℝ) (ht : 0 < t) (i : Fin (k + 1)) : 0 < radii k t i := by
  unfold radii
  by_cases hi : i = 0
  · rw [if_pos hi]; exact ht
  · rw [if_neg hi]
    have h1 : 1 ≤ (i : ℕ) := Nat.one_le_iff_ne_zero.mpr fun hc ↦ hi (Fin.val_eq_zero_iff.mp hc)
    have h2 : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast h1
    linarith

/-- At `t = 0` the radial weights concentrate entirely on the smallest radius. -/
theorem radialWeight_radii_zero (k : ℕ) (i : Fin (k + 1)) :
    radialWeight (radii k 0) i = if i = 0 then 1 else 0 := by
  have hz : ((0 : Fin (k + 1)) : ℕ) = 0 := rfl
  by_cases hi : i = 0
  · subst hi
    rw [if_pos rfl]
    unfold radialWeight
    refine Finset.prod_eq_one fun j hj ↦ ?_
    have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
    have hval : ((j : ℕ) : ℝ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      exact fun hc ↦ hj0 (Fin.val_eq_zero_iff.mp hc)
    simp only [radii_zero, hz, Nat.cast_zero, zero_sub]
    exact div_self (neg_ne_zero.mpr hval)
  · rw [if_neg hi]
    unfold radialWeight
    refine Finset.prod_eq_zero
      (Finset.mem_erase.mpr ⟨Ne.symm hi, Finset.mem_univ 0⟩) ?_
    simp [radii_zero, hz]

/-- At `t = 0` the total variation of the radial weights is exactly one. -/
theorem radialTotal_radii_zero (k : ℕ) : radialTotal (radii k 0) = 1 := by
  unfold radialTotal
  have hterm : ∀ i : Fin (k + 1), |radialWeight (radii k 0) i| =
      if i = 0 then (1 : ℝ) else 0 := by
    intro i
    rw [radialWeight_radii_zero]
    by_cases hi : i = 0 <;> simp [hi]
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i, Finset.sum_ite_eq' Finset.univ (0 : Fin (k + 1))]
  simp

/-- Continuity at a point of a finite product of functions continuous there. -/
theorem continuousAt_finset_prod {ι : Type*} (f : ι → ℝ → ℝ) (x : ℝ)
    (h : ∀ i, ContinuousAt (f i) x) (s : Finset ι) :
    ContinuousAt (fun t ↦ ∏ i ∈ s, f i t) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty]
    exact continuousAt_const
  · intro a s ha ih
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

/-- Continuity at a point of a finite sum of functions continuous there. -/
theorem continuousAt_finset_sum {ι : Type*} (f : ι → ℝ → ℝ) (x : ℝ)
    (h : ∀ i, ContinuousAt (f i) x) (s : Finset ι) :
    ContinuousAt (fun t ↦ ∑ i ∈ s, f i t) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact continuousAt_const
  · intro a s ha ih
    simp only [Finset.sum_insert ha]
    exact (h a).add ih

/-- Each radius depends continuously on the small parameter. -/
theorem radii_continuousAt (k : ℕ) (j : Fin (k + 1)) :
    ContinuousAt (fun t : ℝ ↦ radii k t j) 0 := by
  unfold radii
  by_cases hj : j = 0
  · simp only [if_pos hj]
    exact continuousAt_id
  · simp only [if_neg hj]
    exact continuousAt_const

/-- Each radial weight depends continuously on the small parameter at zero. -/
theorem radialWeight_continuousAt (k : ℕ) (i : Fin (k + 1)) :
    ContinuousAt (fun t : ℝ ↦ radialWeight (radii k t) i) 0 := by
  have hz : ∀ j : Fin (k + 1), radii k 0 j = ((j : ℕ) : ℝ) := radii_zero k
  refine continuousAt_finset_prod
    (fun j t ↦ (-(radii k t j)) / (radii k t i - radii k t j)) 0 (fun j ↦ ?_) _
  show ContinuousAt (fun t : ℝ ↦ (-(radii k t j)) / (radii k t i - radii k t j)) 0
  by_cases hj : j = i
  · subst hj
    have hfun : (fun t : ℝ ↦ (-(radii k t j)) / (radii k t j - radii k t j)) =
        fun _ : ℝ ↦ (0 : ℝ) := by
      funext t
      rw [sub_self, div_zero]
    rw [hfun]
    exact continuousAt_const
  · refine ContinuousAt.div ((radii_continuousAt k j).neg)
      ((radii_continuousAt k i).sub (radii_continuousAt k j)) ?_
    rw [hz i, hz j]
    have hne : (i : ℕ) ≠ (j : ℕ) := fun hc ↦ hj (Fin.val_injective hc).symm
    have : ((i : ℕ) : ℝ) ≠ ((j : ℕ) : ℝ) := by exact_mod_cast hne
    exact sub_ne_zero.mpr this

/-- The total variation of the radial weights is continuous at zero. -/
theorem radialTotal_continuousAt (k : ℕ) :
    ContinuousAt (fun t : ℝ ↦ radialTotal (radii k t)) 0 :=
  continuousAt_finset_sum (fun i t ↦ |radialWeight (radii k t) i|) 0
    (fun i ↦ (radialWeight_continuousAt k i).abs) _

/-- **PL Lemma 7.1, the limit `c_ε → 1`.** For every `δ > 0` there are `k+1` distinct
positive radii whose weights have total variation below `1 + δ`. -/
theorem exists_radii_total_lt (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ radialTotal (radii k t) < 1 + δ := by
  have hcont := radialTotal_continuousAt k
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨η, hη, hball⟩ := hcont δ hδ
  refine ⟨min (η / 2) (1 / 2), lt_min (by linarith) (by norm_num), ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  · have hpos : 0 < min (η / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
    have hdist : dist (min (η / 2) (1 / 2)) 0 < η := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hlt := hball hdist
    rw [Real.dist_eq, radialTotal_radii_zero] at hlt
    linarith [(abs_lt.mp hlt).2]

/-- **PL Theorem 7.2, equation (7.4).** The supremum of the report gap over
moment-matched pairs is the full template gap: for every `η > 0` there are `k+1` distinct
positive radii whose laws share every joint raw moment of total degree at most `k` while
their expected reports differ by more than `F u - F v - η`. -/
theorem radial_gap_approaches_range (k : ℕ) (u v : N → ℝ) (F : (N → ℝ) → ℝ)
    (hF : ∀ t : ℝ, 0 < t → ∀ y : N → ℝ, F (t • y) = F y) (hD : F v ≤ F u)
    (η : ℝ) (hη : 0 < η) :
    ∃ (t : ℝ) (ht : 0 < t) (ht1 : t < 1),
      (∀ α : N → ℕ, ∑ i, α i ≤ k →
          radialExp (radii k t) (radii_injective k t ht ht1) false
              (fun w ↦ monomialEval α (radialPoint (radii k t) u v w)) =
            radialExp (radii k t) (radii_injective k t ht ht1) true
              (fun w ↦ monomialEval α (radialPoint (radii k t) u v w))) ∧
        F u - F v - η ≤
          radialExp (radii k t) (radii_injective k t ht ht1) false
              (fun w ↦ F (radialPoint (radii k t) u v w)) -
            radialExp (radii k t) (radii_injective k t ht ht1) true
              (fun w ↦ F (radialPoint (radii k t) u v w)) := by
  have hD0 : (0 : ℝ) ≤ F u - F v := by linarith
  have hD1 : (0 : ℝ) < F u - F v + 1 := by linarith
  have hδ : 0 < η / (F u - F v + 1) := div_pos hη hD1
  obtain ⟨t, ht, ht1, htot⟩ := exists_radii_total_lt k (η / (F u - F v + 1)) hδ
  have hinj := radii_injective k t ht ht1
  have hpos := radii_pos k t ht
  refine ⟨t, ht, ht1, fun α hα ↦ radial_moment_match (radii k t) hinj u v α hα, ?_⟩
  rw [radial_report_gap (radii k t) hinj hpos u v F hF]
  have hc1 : 1 ≤ radialTotal (radii k t) := one_le_radialTotal _ hinj
  have hcpos : 0 < radialTotal (radii k t) := by linarith
  have hden : (0 : ℝ) < 1 + η / (F u - F v + 1) := by linarith
  have hstep : (F u - F v) / (1 + η / (F u - F v + 1)) ≤
      (F u - F v) / radialTotal (radii k t) := by
    gcongr
  have hfinal : F u - F v - η ≤ (F u - F v) / (1 + η / (F u - F v + 1)) := by
    rw [le_div_iff₀ hden]
    have hexp : (F u - F v - η) * (1 + η / (F u - F v + 1)) =
        (F u - F v - η) * (F u - F v + 1 + η) / (F u - F v + 1) := by
      first
        | (field_simp; ring)
        | field_simp
    rw [hexp, div_le_iff₀ hD1]
    nlinarith
  linarith

end

end Descent.Portability.RadialInterpolation
