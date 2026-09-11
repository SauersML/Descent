/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RadialInterpolation

assert_below Descent.Decision Descent.Program

/-!
# The finite-moment obstruction survives independent coordinates

PL Theorem 7.4. Applying the radial split coordinatewise and taking the product law makes
the outcome coordinates independent while keeping every coordinate moment through degree
`k` matched, hence every mixed joint moment with each coordinate exponent at most `k`
(equation (7.7)). The expected bounded scale-invariant report still converges to the two
template values (equation (7.8)), because the all-small-radius cell carries probability
`(w₀/c_ε)^N`, which tends to one by `RadialInterpolation.radialWeight_continuousAt`.

Scope: the manuscript additionally convolves each coordinate with a uniform law to make
the coordinate distributions absolutely continuous with bounded densities, and invokes
Fubini together with the Lebesgue-null zero set of a nonzero polynomial. That refinement
is measure-theoretic and is NOT formalized here; everything below is the finitely
supported, genuinely independent construction, whose laws are
`Portability.weightedExp` probability vectors on `N → Fin (k+1) × Bool`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.IndependentRadialLaws

open Foundations RadialInterpolation

noncomputable section

variable {k : ℕ} {N : Type*} [Fintype N] [DecidableEq N]

/-- One coordinate's outcome value at a support point of the radial split. -/
def coordValue (r : Fin (k + 1) → ℝ) (a b : ℝ) (z : Fin (k + 1) × Bool) : ℝ :=
  if z.2 then r z.1 * a else r z.1 * b

/-- The master gap identity for a single coordinate, an instance of
`RadialInterpolation.radial_gap_general`. -/
theorem radial_scalar_gap (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r)
    (a b : ℝ) (g : ℝ → ℝ) :
    (∑ z, radialLaw r false z * g (coordValue r a b z)) -
        ∑ z, radialLaw r true z * g (coordValue r a b z) =
      (∑ i, radialWeight r i * (g (r i * a) - g (r i * b))) / radialTotal r :=
  radial_gap_general r hinj (fun z ↦ g (coordValue r a b z))

/-- **PL equation (7.7), one coordinate.** The two one-coordinate laws share every raw
moment through degree `k`. -/
theorem coord_moment_match (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r)
    (a b : ℝ) (m : ℕ) (hm : m ≤ k) :
    (∑ z, radialLaw r false z * coordValue r a b z ^ m) =
      ∑ z, radialLaw r true z * coordValue r a b z ^ m := by
  have hgap := radial_scalar_gap r hinj a b (fun x ↦ x ^ m)
  have hzero : (∑ i, radialWeight r i * ((r i * a) ^ m - (r i * b) ^ m)) = 0 := by
    have hterm : ∀ i : Fin (k + 1),
        radialWeight r i * ((r i * a) ^ m - (r i * b) ^ m) =
          (a ^ m - b ^ m) * (radialWeight r i * r i ^ m) := by
      intro i
      rw [mul_pow, mul_pow]
      ring
    rw [Finset.sum_congr rfl fun i _ ↦ hterm i, ← Finset.mul_sum]
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · rw [radialWeight_moment r hinj h hm, mul_zero]
  rw [hzero, zero_div] at hgap
  linarith

/-- The product law over independent coordinates. -/
def productLaw (r : Fin (k + 1) → ℝ) (s : Bool) (ω : N → Fin (k + 1) × Bool) : ℝ :=
  ∏ i, radialLaw r s (ω i)

/-- The product law is nonnegative. -/
theorem productLaw_nonneg (r : Fin (k + 1) → ℝ) (s : Bool)
    (ω : N → Fin (k + 1) × Bool) : 0 ≤ productLaw r s ω :=
  Finset.prod_nonneg fun i _ ↦ radialLaw_nonneg r s (ω i)

/-- Expectation of a coordinatewise product factorizes: the coordinates are
independent. -/
theorem productLaw_expectation (r : Fin (k + 1) → ℝ) (s : Bool)
    (h : N → (Fin (k + 1) × Bool) → ℝ) :
    (∑ ω : N → Fin (k + 1) × Bool, productLaw r s ω * ∏ i, h i (ω i)) =
      ∏ i, ∑ z, radialLaw r s z * h i z := by
  have hpi : (Fintype.piFinset fun _ : N ↦ (Finset.univ : Finset (Fin (k + 1) × Bool))) =
      Finset.univ := by
    ext ω
    simp
  have hkey := Finset.sum_prod_piFinset (R := ℝ) (ι := N)
    (Finset.univ : Finset (Fin (k + 1) × Bool)) (fun i z ↦ radialLaw r s z * h i z)
  rw [hpi] at hkey
  rw [← hkey]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [productLaw, ← Finset.prod_mul_distrib]

/-- The product law is a probability law. -/
theorem productLaw_sum (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r) (s : Bool) :
    ∑ ω : N → Fin (k + 1) × Bool, productLaw r s ω = 1 := by
  have hone := productLaw_expectation (N := N) r s (fun _ _ ↦ (1 : ℝ))
  simp only [Finset.prod_const_one, mul_one] at hone
  rw [hone]
  refine Finset.prod_eq_one fun i _ ↦ ?_
  simpa using radialLaw_sum r hinj s

/-- The two product expectations of PL Theorem 7.4. -/
def productExp (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r) (s : Bool) :
    ExpFunctional (N → Fin (k + 1) × Bool) :=
  weightedExp (productLaw r s) (productLaw_nonneg r s) (productLaw_sum r hinj s)

/-- The outcome vector of a product draw: coordinate `i` sits on its own ray. -/
def productOutcome (r : Fin (k + 1) → ℝ) (u v : N → ℝ) (ω : N → Fin (k + 1) × Bool) :
    N → ℝ := fun i ↦ coordValue r (u i) (v i) (ω i)

/-- **PL equation (7.7).** The two product laws share every joint raw moment whose
coordinate exponents are all at most `k`. -/
theorem product_moment_match (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r)
    (u v : N → ℝ) (α : N → ℕ) (hα : ∀ i, α i ≤ k) :
    productExp r hinj false (fun ω ↦ monomialEval α (productOutcome r u v ω)) =
      productExp r hinj true (fun ω ↦ monomialEval α (productOutcome r u v ω)) := by
  have hmono : ∀ s : Bool,
      (∑ ω : N → Fin (k + 1) × Bool,
        productLaw r s ω * monomialEval α (productOutcome r u v ω)) =
        ∏ i, ∑ z, radialLaw r s z * coordValue r (u i) (v i) z ^ α i := by
    intro s
    rw [← productLaw_expectation r s (fun i z ↦ coordValue r (u i) (v i) z ^ α i)]
    rfl
  simp only [productExp, weightedExp_apply]
  rw [hmono false, hmono true]
  exact Finset.prod_congr rfl fun i _ ↦
    coord_moment_match r hinj (u i) (v i) (α i) (hα i)

/-- A probability average is close to the value at a heavy atom. -/
theorem exp_close_to_point {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hs : ∑ ω, p ω = 1) (h : Ω → ℝ) (M : ℝ)
    (hM : ∀ ω, |h ω| ≤ M) (ω₀ : Ω) :
    |(∑ ω, p ω * h ω) - h ω₀| ≤ 2 * M * (1 - p ω₀) := by
  have htot := Finset.add_sum_erase Finset.univ p (Finset.mem_univ ω₀)
  have hsplit : (∑ ω, p ω * h ω) =
      p ω₀ * h ω₀ + ∑ ω ∈ Finset.univ.erase ω₀, p ω * h ω :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ ω₀)).symm
  have hp1 : p ω₀ ≤ 1 := by
    have hnn : 0 ≤ ∑ ω ∈ Finset.univ.erase ω₀, p ω := Finset.sum_nonneg fun ω _ ↦ hp ω
    linarith [hs, htot]
  have hrest : |∑ ω ∈ Finset.univ.erase ω₀, p ω * h ω| ≤ (1 - p ω₀) * M := by
    calc |∑ ω ∈ Finset.univ.erase ω₀, p ω * h ω| ≤
          ∑ ω ∈ Finset.univ.erase ω₀, |p ω * h ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ω ∈ Finset.univ.erase ω₀, p ω * M := by
          refine Finset.sum_le_sum fun ω _ ↦ ?_
          rw [abs_mul, abs_of_nonneg (hp ω)]
          exact mul_le_mul_of_nonneg_left (hM ω) (hp ω)
      _ = (1 - p ω₀) * M := by
          rw [← Finset.sum_mul]
          congr 1
          linarith [hs, htot]
  have h1 := abs_le.mp hrest
  have h2 := abs_le.mp (hM ω₀)
  have hq : (0 : ℝ) ≤ 1 - p ω₀ := by linarith
  have hprod1 : 0 ≤ (1 - p ω₀) * (M - h ω₀) := mul_nonneg hq (by linarith [h2.2])
  have hprod2 : 0 ≤ (1 - p ω₀) * (M + h ω₀) := mul_nonneg hq (by linarith [h2.1])
  rw [hsplit, abs_le]
  constructor <;> nlinarith [h1.1, h1.2, hprod1, hprod2]

/-- The one-coordinate mass of the small-radius cell, common to both product laws. -/
theorem radialLaw_cell (r : Fin (k + 1) → ℝ) (s : Bool) :
    radialLaw r s (0, !s) =
      (|radialWeight r 0| + radialWeight r 0) / 2 / radialTotal r := by
  cases s <;> rfl

omit [Fintype N] [DecidableEq N] in
/-- On the all-small-radius cell the outcome vector is the template, rescaled. -/
theorem productOutcome_cell (r : Fin (k + 1) → ℝ) (u v : N → ℝ) (s : Bool) :
    productOutcome r u v (fun _ ↦ (0, !s)) = r 0 • (if s then v else u) := by
  funext i
  cases s <;> simp [productOutcome, coordValue]

/-- **PL equation (7.8), quantitative form.** The expected report under either product
law is within `2M(1 - (w₀/c)^N)` of the corresponding template report. -/
theorem product_concentration (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r)
    (hpos : ∀ i, 0 < r i) (s : Bool) (u v : N → ℝ) (F : (N → ℝ) → ℝ) (M : ℝ)
    (hM : ∀ y, |F y| ≤ M) (hF : ∀ t : ℝ, 0 < t → ∀ y : N → ℝ, F (t • y) = F y) :
    |productExp r hinj s (fun ω ↦ F (productOutcome r u v ω)) -
        F (if s then v else u)| ≤
      2 * M * (1 - ((|radialWeight r 0| + radialWeight r 0) / 2 / radialTotal r) ^
        Fintype.card N) := by
  have hcell : productLaw r s (fun _ : N ↦ ((0, !s) : Fin (k + 1) × Bool)) =
      ((|radialWeight r 0| + radialWeight r 0) / 2 / radialTotal r) ^ Fintype.card N := by
    rw [productLaw]
    simp only [radialLaw_cell r s]
    rw [Finset.prod_const, Finset.card_univ]
  have hval : F (productOutcome r u v (fun _ : N ↦ ((0, !s) : Fin (k + 1) × Bool))) =
      F (if s then v else u) := by
    rw [productOutcome_cell]
    exact hF (r 0) (hpos 0) _
  have hmain := exp_close_to_point (productLaw r s) (productLaw_nonneg r s)
    (productLaw_sum r hinj s) (fun ω ↦ F (productOutcome r u v ω)) M
    (fun ω ↦ hM _) (fun _ : N ↦ ((0, !s) : Fin (k + 1) × Bool))
  rw [hval, hcell] at hmain
  exact hmain

/-- The small-radius cell mass of the `radii` family. -/
def cellMass (k : ℕ) (t : ℝ) : ℝ :=
  (|radialWeight (radii k t) 0| + radialWeight (radii k t) 0) / 2 /
    radialTotal (radii k t)

/-- At `t = 0` the cell carries all the mass. -/
theorem cellMass_zero (k : ℕ) : cellMass k 0 = 1 := by
  unfold cellMass
  rw [radialWeight_radii_zero, radialTotal_radii_zero]
  norm_num

/-- The cell mass depends continuously on the small parameter at zero. -/
theorem cellMass_continuousAt (k : ℕ) : ContinuousAt (fun t : ℝ ↦ cellMass k t) 0 := by
  have hw := radialWeight_continuousAt k 0
  have hc := radialTotal_continuousAt k
  have hne : radialTotal (radii k 0) ≠ 0 := by
    rw [radialTotal_radii_zero]; norm_num
  exact ContinuousAt.div (((hw.abs).add hw).div_const 2) hc hne

/-- **PL Theorem 7.4, independent finite-support core.** For every `k` and every `η > 0`
there are two product laws with independent coordinates sharing every joint raw moment
whose coordinate exponents are at most `k`, whose expected bounded scale-invariant
reports are within `η` of the two template reports. -/
theorem independent_radial_obstruction (k : ℕ) (u v : N → ℝ) (F : (N → ℝ) → ℝ) (M : ℝ)
    (hM : ∀ y, |F y| ≤ M) (hF : ∀ t : ℝ, 0 < t → ∀ y : N → ℝ, F (t • y) = F y)
    (η : ℝ) (hη : 0 < η) :
    ∃ (t : ℝ) (ht : 0 < t) (ht1 : t < 1),
      (∀ α : N → ℕ, (∀ i, α i ≤ k) →
          productExp (radii k t) (radii_injective k t ht ht1) false
              (fun ω ↦ monomialEval α (productOutcome (radii k t) u v ω)) =
            productExp (radii k t) (radii_injective k t ht ht1) true
              (fun ω ↦ monomialEval α (productOutcome (radii k t) u v ω))) ∧
        |productExp (radii k t) (radii_injective k t ht ht1) false
            (fun ω ↦ F (productOutcome (radii k t) u v ω)) - F u| ≤ η ∧
        |productExp (radii k t) (radii_injective k t ht ht1) true
            (fun ω ↦ F (productOutcome (radii k t) u v ω)) - F v| ≤ η := by
  have hcont : ContinuousAt
      (fun t : ℝ ↦ 2 * M * (1 - (cellMass k t) ^ Fintype.card N)) 0 :=
    (continuousAt_const.mul ((continuousAt_const.sub
      ((cellMass_continuousAt k).pow (Fintype.card N)))))
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hball⟩ := hcont η hη
  have hpos : 0 < min (δ / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
  have ht1 : min (δ / 2) (1 / 2) < 1 :=
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hdist : dist (min (δ / 2) (1 / 2)) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hlt := hball hdist
  rw [Real.dist_eq, cellMass_zero] at hlt
  simp only [one_pow, sub_self, mul_zero, sub_zero] at hlt
  refine ⟨min (δ / 2) (1 / 2), hpos, ht1, fun α hα ↦
    product_moment_match _ (radii_injective k _ hpos ht1) u v α hα, ?_, ?_⟩
  · have hbound := product_concentration (radii k (min (δ / 2) (1 / 2)))
      (radii_injective k _ hpos ht1) (radii_pos k _ hpos) false u v F M hM hF
    simp only [if_neg (by norm_num : ¬(false = true))] at hbound
    have hle : 2 * M * (1 - (cellMass k (min (δ / 2) (1 / 2))) ^ Fintype.card N) ≤ η :=
      le_of_lt (lt_of_le_of_lt (le_abs_self _) hlt)
    exact le_trans hbound hle
  · have hbound := product_concentration (radii k (min (δ / 2) (1 / 2)))
      (radii_injective k _ hpos ht1) (radii_pos k _ hpos) true u v F M hM hF
    have hle : 2 * M * (1 - (cellMass k (min (δ / 2) (1 / 2))) ^ Fintype.card N) ≤ η :=
      le_of_lt (lt_of_le_of_lt (le_abs_self _) hlt)
    exact le_trans hbound hle

end

end Descent.Portability.IndependentRadialLaws
