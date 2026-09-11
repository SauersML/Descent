/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BinomialAggregateEnvelope
import Descent.Portability.ChronologyReportLaw
import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.ContinuousMap.Weierstrass

assert_below Descent.Decision Descent.Program

/-!
# Spectral constraints on the admixture coupling

NOTE1 section 6.3 reads the normalised coupling of an admixture chronology as the Laplace
transform of the recombination-exposure law `ν` carried by the immigration increments, and
records what that forces. This module formalises those constraints for a finitely supported
exposure law, taken as a `FiniteReportLaw (Fin n)` of weights together with an exposure vector
`b : Fin n → ℝ`; the transform is then the finite sum `∑ wᵢ e^{-λ bᵢ}`.

Proved here. NOTE1 (35), complete monotonicity: the `k`-th iterated derivative in `λ` is
`∑ wᵢ (-bᵢ)^k e^{-λ bᵢ}`, so `(-1)^k` times it is nonnegative whenever the exposures are;
and the transform is log-convex in the midpoint sense, by Cauchy-Schwarz on the finite sum.
NOTE1 (36), the two-sided bound at a known mean exposure `b̄` with support in `[0, R]` and
`R > 0`: the Jensen lower bound `e^{-λ b̄} ≤ ∑ wᵢ e^{-λ bᵢ}` and the chord upper bound
`∑ wᵢ e^{-λ bᵢ} ≤ 1 - b̄/R + (b̄/R) e^{-λ R}`. Both are sharp: the point mass at `b̄` attains
the lower bound with equality, and the two-point mixture on the endpoints `0` and `R` with
mean `b̄` attains the upper bound with equality. Finally, the two identifications of NOTE1
section 6.3: the square of the transform is the transform of the law of a sum of two
independent exposures, and the population AUC of the report law of NOTE1 (31) at coupling
`∑ wᵢ e^{-λ bᵢ}` is the transform of the half-and-half mixture of the point mass at exposure
zero with the exposure law.

Identifiability, the last claim of NOTE1 section 6.3, is proved for finite laws. At an integer
scale `k` the transform is `∑_b ν{b} (e^{-b})^k`, where `exposureMass` is the mass the law places
at the level `b`. The characters `k ↦ (e^{-b})^k` of the additive monoid of natural numbers are
distinct for distinct `b`, hence linearly independent (Dedekind). Two forms are proved: two
finite laws whose transforms agree at every integer scale `λ = 0, 1, 2, …`
(`exposureMass_eq_of_exposureLaplace_natCast_eq`), or at every scale `λ ≥ 0`
(`exposureMass_eq_of_exposureLaplace_eq`), place the same mass at every exposure level. No
support bound is used, so this covers every finitely supported law on `[0, R]` as in the note.

General measures. For an arbitrary measure `ν` the transform is `measureLaplace ν λ`, and a
finite law enters through `lawMeasure`, whose transform is `exposureLaplace`. NOTE1 (36) is
proved in that generality: for a probability measure carried by `[0, R]`, Jensen's lower bound
(`exp_neg_mean_le_measureLaplace`, through `ConvexOn.map_integral_le`) and the chord upper
bound (`measureLaplace_le_chord`), attained by the point mass at the mean and by the endpoint
mixture. So is NOTE1 (35) for a finite measure carried by `[0, R]`: differentiating under the
integral (`hasDerivAt_momentLaplace`) gives every iterated derivative as a moment transform
(`iteratedDeriv_measureLaplace`), hence complete monotonicity
(`sign_iteratedDeriv_measureLaplace`), and a nonnegative quadratic gives midpoint log-convexity
(`measureLaplace_sq_le_mul`). The squared transform is the transform of the convolution
`ν ∗ ν` (`measureLaplace_conv`). Identifiability holds for every finite measure carried by
`[0, R]`: two such laws whose transforms agree at the integer scales `λ = 0, 1, 2, …`
(`measure_eq_of_measureLaplace_natCast_eq`), or at every `λ ≥ 0`
(`measure_eq_of_measureLaplace_eq`), are equal. A polynomial in `e^{-b}` integrates to a
combination of transforms at integer scales (`integral_eval_exp_neg`), and by Weierstrass on
`[e^{-R}, 1]` such polynomials approximate every bounded continuous function uniformly on
`[0, R]`; this replaces the moment argument of NOTE1 section 6.3 by the same density argument
in the variable `e^{-b}`. That calendar-time rates are not identified is proved in
`AdmixtureChronologyLaw`. Nothing here identifies `ν` from data.

## Empirical status

None. The bodies here are algebra and one-variable calculus: the exposure law is a stated
parameter of a stated mechanism and no measurement enters any statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ExposureLaplaceConstraints

noncomputable section

/-- The Laplace transform of a finitely supported exposure law: the average of the
recombination-survival factor `e^{-λ b}` over the exposure weights. -/
def exposureLaplace {n : ℕ} (law : FiniteReportLaw (Fin n)) (exposure : Fin n → ℝ)
    (lam : ℝ) : ℝ :=
  law.expectation fun index ↦ Real.exp (-(lam * exposure index))

/-- At zero scaling no recombination survives to act, and the transform is one. -/
theorem exposureLaplace_zero {n : ℕ} (law : FiniteReportLaw (Fin n))
    (exposure : Fin n → ℝ) : exposureLaplace law exposure 0 = 1 := by
  unfold exposureLaplace FiniteReportLaw.expectation
  simp [law.mass_sum]

/-- Expectation of an affine function of the exposures. -/
private theorem expectation_affine {n : ℕ} (law : FiniteReportLaw (Fin n))
    (value : Fin n → ℝ) (intercept slope : ℝ) :
    law.expectation (fun index ↦ intercept + slope * value index) =
      intercept + slope * law.expectation value := by
  have hstep : ∀ index : Fin n, law.mass index * (intercept + slope * value index) =
      intercept * law.mass index + slope * (law.mass index * value index) := by
    intro index
    ring
  unfold FiniteReportLaw.expectation
  rw [Finset.sum_congr rfl (fun index _ ↦ hstep index), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, law.mass_sum, mul_one]

/-- NOTE1 (36), lower bound: the transform is at least the survival factor of the mean
exposure. This is Jensen for the exponential, obtained from the tangent-line bound. -/
theorem exp_neg_mean_le_exposureLaplace {n : ℕ} (law : FiniteReportLaw (Fin n))
    (exposure : Fin n → ℝ) (lam : ℝ) :
    Real.exp (-(lam * law.expectation exposure)) ≤ exposureLaplace law exposure lam := by
  have htangent : ∀ index : Fin n,
      Real.exp (-(lam * law.expectation exposure)) *
          (1 + lam * law.expectation exposure - lam * exposure index) ≤
        Real.exp (-(lam * exposure index)) := by
    intro index
    have hbase := Real.add_one_le_exp
      (-(lam * exposure index) + lam * law.expectation exposure)
    have hpos : (0 : ℝ) < Real.exp (-(lam * law.expectation exposure)) := Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_left hbase hpos.le
    rw [← Real.exp_add, show -(lam * law.expectation exposure) +
      (-(lam * exposure index) + lam * law.expectation exposure) =
      -(lam * exposure index) from by ring] at hmul
    nlinarith [hmul]
  have hsum : law.expectation (fun index ↦
      Real.exp (-(lam * law.expectation exposure)) *
        (1 + lam * law.expectation exposure - lam * exposure index)) ≤
      exposureLaplace law exposure lam := by
    unfold exposureLaplace FiniteReportLaw.expectation
    exact Finset.sum_le_sum fun index _ ↦
      mul_le_mul_of_nonneg_left (htangent index) (law.mass_nonneg index)
  have hvalue : law.expectation (fun index ↦
      Real.exp (-(lam * law.expectation exposure)) *
        (1 + lam * law.expectation exposure - lam * exposure index)) =
      Real.exp (-(lam * law.expectation exposure)) := by
    have hrewrite : (fun index ↦ Real.exp (-(lam * law.expectation exposure)) *
        (1 + lam * law.expectation exposure - lam * exposure index)) =
        (fun index ↦ Real.exp (-(lam * law.expectation exposure)) *
          (1 + lam * law.expectation exposure) +
            (-(Real.exp (-(lam * law.expectation exposure)) * lam)) * exposure index) := by
      funext index
      ring
    rw [hrewrite, expectation_affine]
    ring
  linarith [hsum, hvalue]

/-- The chord bound for the exponential on `[0, R]`: at an exposure inside the interval the
survival factor lies below the straight line joining its endpoint values. -/
theorem exp_chord_bound (bound lam exposure : ℝ) (hbound : 0 < bound)
    (hlow : 0 ≤ exposure) (hhigh : exposure ≤ bound) :
    Real.exp (-(lam * exposure)) ≤
      1 - exposure / bound + exposure / bound * Real.exp (-(lam * bound)) := by
  have hfrac0 : 0 ≤ exposure / bound := div_nonneg hlow hbound.le
  have hfrac1 : exposure / bound ≤ 1 := (div_le_one hbound).mpr hhigh
  have hconvex := convexOn_exp.2 (Set.mem_univ (0 : ℝ))
    (Set.mem_univ (-(lam * bound))) (by linarith : (0 : ℝ) ≤ 1 - exposure / bound) hfrac0
    (by ring)
  have harg : (1 - exposure / bound) • (0 : ℝ) + (exposure / bound) • (-(lam * bound)) =
      -(lam * exposure) := by
    simp only [smul_eq_mul, mul_zero, zero_add]
    field_simp
  rw [harg] at hconvex
  simp only [smul_eq_mul, Real.exp_zero, mul_one] at hconvex
  linarith [hconvex]

/-- NOTE1 (36), upper bound: with exposures confined to `[0, R]` the transform is at most the
endpoint chord evaluated at the mean exposure. -/
theorem exposureLaplace_le_chord {n : ℕ} (law : FiniteReportLaw (Fin n))
    (exposure : Fin n → ℝ) (bound lam : ℝ) (hbound : 0 < bound)
    (hlow : ∀ index, 0 ≤ exposure index) (hhigh : ∀ index, exposure index ≤ bound) :
    exposureLaplace law exposure lam ≤
      1 - law.expectation exposure / bound +
        law.expectation exposure / bound * Real.exp (-(lam * bound)) := by
  have hbne : bound ≠ 0 := ne_of_gt hbound
  have hsum : exposureLaplace law exposure lam ≤
      law.expectation (fun index ↦ 1 - exposure index / bound +
        exposure index / bound * Real.exp (-(lam * bound))) := by
    unfold exposureLaplace FiniteReportLaw.expectation
    exact Finset.sum_le_sum fun index _ ↦
      mul_le_mul_of_nonneg_left
        (exp_chord_bound bound lam (exposure index) hbound (hlow index) (hhigh index))
        (law.mass_nonneg index)
  have hvalue : law.expectation (fun index ↦ 1 - exposure index / bound +
      exposure index / bound * Real.exp (-(lam * bound))) =
      1 - law.expectation exposure / bound +
        law.expectation exposure / bound * Real.exp (-(lam * bound)) := by
    have hrewrite : (fun index ↦ 1 - exposure index / bound +
        exposure index / bound * Real.exp (-(lam * bound))) =
        (fun index ↦ 1 +
          ((Real.exp (-(lam * bound)) - 1) / bound) * exposure index) := by
      funext index
      field_simp
      ring
    rw [hrewrite, expectation_affine]
    field_simp
    ring
  linarith [hsum, hvalue]

/-- The Jensen bound is sharp: a point mass attains it with equality. -/
theorem exposureLaplace_pointMass {n : ℕ} (selected : Fin n) (exposure : Fin n → ℝ)
    (lam : ℝ) :
    exposureLaplace (FiniteReportLaw.pointMass selected) exposure lam =
      Real.exp (-(lam * (FiniteReportLaw.pointMass selected).expectation exposure)) := by
  unfold exposureLaplace
  rw [FiniteReportLaw.expectation_pointMass, FiniteReportLaw.expectation_pointMass]

/-- The two-point law on the endpoints of `[0, R]` with prescribed mean exposure. -/
def endpointMixture (bound mean : ℝ) (hlow : 0 ≤ mean) (hhigh : mean ≤ bound)
    (hbound : 0 < bound) : FiniteReportLaw (Fin 2) where
  mass := ![1 - mean / bound, mean / bound]
  mass_nonneg := by
    have hfrac0 : 0 ≤ mean / bound := div_nonneg hlow hbound.le
    have hfrac1 : mean / bound ≤ 1 := (div_le_one hbound).mpr hhigh
    intro index
    fin_cases index
    · simpa using by linarith
    · simpa using hfrac0
  mass_sum := by
    simp [Fin.sum_univ_two]

/-- The exposures of the two-point endpoint law: none and the whole recombination total. -/
def endpointExposure (bound : ℝ) : Fin 2 → ℝ := ![0, bound]

/-- The endpoint law has exactly the prescribed mean exposure. -/
theorem expectation_endpointExposure (bound mean : ℝ) (hlow : 0 ≤ mean)
    (hhigh : mean ≤ bound) (hbound : 0 < bound) :
    (endpointMixture bound mean hlow hhigh hbound).expectation (endpointExposure bound) =
      mean := by
  have hne : bound ≠ 0 := ne_of_gt hbound
  unfold FiniteReportLaw.expectation endpointMixture endpointExposure
  rw [Fin.sum_univ_two]
  simp [hne]

/-- The chord bound is sharp: the endpoint law attains it with equality. -/
theorem exposureLaplace_endpointMixture (bound mean lam : ℝ) (hlow : 0 ≤ mean)
    (hhigh : mean ≤ bound) (hbound : 0 < bound) :
    exposureLaplace (endpointMixture bound mean hlow hhigh hbound)
        (endpointExposure bound) lam =
      1 - mean / bound + mean / bound * Real.exp (-(lam * bound)) := by
  unfold exposureLaplace FiniteReportLaw.expectation endpointMixture endpointExposure
  rw [Fin.sum_univ_two]
  simp

/-- At an integer recombination total `n` the endpoint exposures are the aligned-locus counts of
the synchronous coupling in `BinomialAggregateEnvelope`, read as reals: both are the
all-or-nothing vector `(0, n)`. -/
theorem endpointExposure_natCast (count : ℕ) :
    endpointExposure (count : ℝ) =
      fun index ↦ (BinomialAggregateEnvelope.syncCount count index : ℝ) := by
  funext index
  fin_cases index <;> simp [endpointExposure, BinomialAggregateEnvelope.syncCount]

/-- NOTE1 (35): every iterated derivative of the transform is the corresponding exposure
moment, with the sign of `(-1)^k`. -/
theorem iteratedDeriv_exposureLaplace {n : ℕ} (law : FiniteReportLaw (Fin n))
    (exposure : Fin n → ℝ) (order : ℕ) :
    iteratedDeriv order (exposureLaplace law exposure) =
      fun lam ↦ ∑ index, law.mass index * (-(exposure index)) ^ order *
        Real.exp (-(lam * exposure index)) := by
  induction order with
  | zero =>
    funext lam
    simp [iteratedDeriv_zero, exposureLaplace, FiniteReportLaw.expectation]
  | succ order ih =>
    rw [iteratedDeriv_succ, ih]
    funext lam
    have hterm : ∀ index ∈ (Finset.univ : Finset (Fin n)), HasDerivAt
        (fun value ↦ law.mass index * (-(exposure index)) ^ order *
          Real.exp (-(value * exposure index)))
        (law.mass index * (-(exposure index)) ^ (order + 1) *
          Real.exp (-(lam * exposure index))) lam := by
      intro index _
      have hlinear : HasDerivAt (fun value : ℝ ↦ -(value * exposure index))
          (-(exposure index)) lam := by
        have hstep := ((hasDerivAt_id lam).mul_const (exposure index)).neg
        simpa using hstep
      refine (hlinear.exp.const_mul
        (law.mass index * (-(exposure index)) ^ order)).congr_deriv ?_
      ring
    exact (HasDerivAt.fun_sum hterm).deriv

/-- NOTE1 (35), the sign pattern: the transform of a nonnegative exposure law is completely
monotone. -/
theorem sign_iteratedDeriv_exposureLaplace {n : ℕ} (law : FiniteReportLaw (Fin n))
    (exposure : Fin n → ℝ) (hnonneg : ∀ index, 0 ≤ exposure index) (order : ℕ) (lam : ℝ) :
    0 ≤ (-1 : ℝ) ^ order * iteratedDeriv order (exposureLaplace law exposure) lam := by
  rw [iteratedDeriv_exposureLaplace, Finset.mul_sum]
  refine Finset.sum_nonneg fun index _ ↦ ?_
  have hpow : ((-1 : ℝ)) ^ order * (-(exposure index)) ^ order = exposure index ^ order := by
    rw [← mul_pow, show (-1 : ℝ) * -(exposure index) = exposure index from by ring]
  have hvalue : (-1 : ℝ) ^ order * (law.mass index * (-(exposure index)) ^ order *
      Real.exp (-(lam * exposure index))) =
      law.mass index * exposure index ^ order * Real.exp (-(lam * exposure index)) := by
    rw [← hpow]
    ring
  rw [hvalue]
  exact mul_nonneg (mul_nonneg (law.mass_nonneg index) (pow_nonneg (hnonneg index) order))
    (Real.exp_pos _).le

/-- NOTE1 (35), log-convexity: the transform at a midpoint is dominated in square by the
product of its endpoint values, by Cauchy-Schwarz on the exposure weights. -/
theorem exposureLaplace_sq_le_mul {n : ℕ} (law : FiniteReportLaw (Fin n))
    (exposure : Fin n → ℝ) (lam mu : ℝ) :
    exposureLaplace law exposure ((lam + mu) / 2) ^ 2 ≤
      exposureLaplace law exposure lam * exposureLaplace law exposure mu := by
  classical
  set left : Fin n → ℝ := fun index ↦
    Real.sqrt (law.mass index) * Real.exp (-(lam * exposure index) / 2) with hleft
  set right : Fin n → ℝ := fun index ↦
    Real.sqrt (law.mass index) * Real.exp (-(mu * exposure index) / 2) with hright
  have hcross : ∀ index : Fin n, left index * right index =
      law.mass index * Real.exp (-((lam + mu) / 2 * exposure index)) := by
    intro index
    rw [hleft, hright]
    simp only
    rw [mul_mul_mul_comm, Real.mul_self_sqrt (law.mass_nonneg index), ← Real.exp_add,
      show -(lam * exposure index) / 2 + -(mu * exposure index) / 2 =
        -((lam + mu) / 2 * exposure index) from by ring]
  have hsquare : ∀ (scale : ℝ) (index : Fin n),
      (Real.sqrt (law.mass index) * Real.exp (-(scale * exposure index) / 2)) ^ 2 =
        law.mass index * Real.exp (-(scale * exposure index)) := by
    intro scale index
    rw [mul_pow, Real.sq_sqrt (law.mass_nonneg index), pow_two, ← Real.exp_add,
      show -(scale * exposure index) / 2 + -(scale * exposure index) / 2 =
        -(scale * exposure index) from by ring]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ left right
  rw [Finset.sum_congr rfl (fun index _ ↦ hcross index),
    Finset.sum_congr rfl (fun index _ ↦ hsquare lam index),
    Finset.sum_congr rfl (fun index _ ↦ hsquare mu index)] at hcs
  exact hcs

/-- The square of the transform is the transform of the law of a sum of two independent
exposures, which is NOTE1 section 6.3 read on the self-convolution of the exposure law. -/
theorem exposureLaplace_joint_add {n : ℕ} (law : FiniteReportLaw (Fin n))
    (exposure : Fin n → ℝ) (lam : ℝ) :
    (law.joint fun _ ↦ law).expectation
        (fun pair ↦ Real.exp (-(lam * (exposure pair.1 + exposure pair.2)))) =
      exposureLaplace law exposure lam ^ 2 := by
  have hterm : ∀ first second : Fin n,
      Real.exp (-(lam * (exposure first + exposure second))) =
        Real.exp (-(lam * exposure first)) * Real.exp (-(lam * exposure second)) := by
    intro first second
    rw [← Real.exp_add]
    congr 1
    ring
  rw [FiniteReportLaw.expectation_joint]
  simp only [exposureLaplace, FiniteReportLaw.expectation]
  rw [pow_two, Finset.sum_mul]
  refine Finset.sum_congr rfl fun first _ ↦ ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun second _ ↦ ?_
  rw [hterm first second]
  ring

/-- The half-and-half mixture of the point mass at exposure zero with a finite exposure law,
whose transform NOTE1 section 6.3 identifies with the AUC. -/
def zeroMixture {n : ℕ} (law : FiniteReportLaw (Fin n)) :
    FiniteReportLaw (Option (Fin n)) where
  mass := fun index ↦
    match index with
    | none => 1 / 2
    | some component => law.mass component / 2
  mass_nonneg := by
    rintro (_ | component)
    · norm_num
    · exact div_nonneg (law.mass_nonneg component) (by norm_num)
  mass_sum := by
    rw [Fintype.sum_option]
    simp only [← Finset.sum_div, law.mass_sum]
    norm_num

/-- The mixture puts half its mass on the added point. -/
@[simp] theorem zeroMixture_mass_none {n : ℕ} (law : FiniteReportLaw (Fin n)) :
    (zeroMixture law).mass none = 1 / 2 := rfl

/-- The mixture halves the original weights. -/
@[simp] theorem zeroMixture_mass_some {n : ℕ} (law : FiniteReportLaw (Fin n))
    (component : Fin n) :
    (zeroMixture law).mass (some component) = law.mass component / 2 := rfl

/-- The exposures of the mixture: the added point carries no exposure. -/
def zeroMixtureExposure {n : ℕ} (exposure : Fin n → ℝ) : Option (Fin n) → ℝ := fun index ↦
  match index with
  | none => 0
  | some component => exposure component

/-- The added point carries no exposure. -/
@[simp] theorem zeroMixtureExposure_none {n : ℕ} (exposure : Fin n → ℝ) :
    zeroMixtureExposure exposure none = 0 := rfl

/-- The original points keep their exposure. -/
@[simp] theorem zeroMixtureExposure_some {n : ℕ} (exposure : Fin n → ℝ)
    (component : Fin n) :
    zeroMixtureExposure exposure (some component) = exposure component := rfl

/-- The transform of the zero mixture is the AUC expression `(1 + C) / 2`. -/
theorem exposureLaplace_zeroMixture {n : ℕ} (law : FiniteReportLaw (Fin n))
    (exposure : Fin n → ℝ) (lam : ℝ) :
    (zeroMixture law).expectation
        (fun index ↦ Real.exp (-(lam * zeroMixtureExposure exposure index))) =
      (1 + exposureLaplace law exposure lam) / 2 := by
  have hterm : ∀ component : Fin n,
      law.mass component / 2 * Real.exp (-(lam * exposure component)) =
        law.mass component * Real.exp (-(lam * exposure component)) / 2 := by
    intro component
    ring
  simp only [exposureLaplace, FiniteReportLaw.expectation]
  rw [Fintype.sum_option]
  simp only [zeroMixture_mass_none, zeroMixture_mass_some, zeroMixtureExposure_none,
    zeroMixtureExposure_some, mul_zero, neg_zero, Real.exp_zero, mul_one]
  rw [Finset.sum_congr rfl (fun component _ ↦ hterm component), ← Finset.sum_div]
  ring

/-- NOTE1 section 6.3: the population AUC of the report law of NOTE1 (31) at a coupling given
by an exposure transform is the transform of the half-and-half mixture of the point mass at
zero exposure with the exposure law. -/
theorem populationAUC_eq_zeroMixture_laplace {n : ℕ} (law : FiniteReportLaw (Fin n))
    (exposure : Fin n → ℝ) (lam donor : ℝ) (hp0 : 0 ≤ donor) (hp1 : donor ≤ 1)
    (hC0 : 0 ≤ exposureLaplace law exposure lam)
    (hC1 : exposureLaplace law exposure lam ≤ 1) (hlow : 0 < donor)
    (hhigh : donor < 1) :
    ChronologyReportLaw.populationAUC
        (ChronologyReportLaw.chronologyLaw donor (exposureLaplace law exposure lam)
          hp0 hp1 hC0 hC1) =
      (zeroMixture law).expectation
        (fun index ↦ Real.exp (-(lam * zeroMixtureExposure exposure index))) := by
  rw [ChronologyReportLaw.populationAUC_chronologyLaw donor
    (exposureLaplace law exposure lam) hp0 hp1 hC0 hC1 hlow hhigh,
    exposureLaplace_zeroMixture]

/-- The mass a finite exposure law places at the exposure level `level`. -/
def exposureMass {n : ℕ} (law : FiniteReportLaw (Fin n)) (exposure : Fin n → ℝ)
    (level : ℝ) : ℝ :=
  ∑ index ∈ Finset.univ.filter (fun index ↦ exposure index = level), law.mass index

/-- Assumes: a finite set of levels containing every exposure of the law. The transform at an
integer scale `k` is `∑_b ν{b} (e^{-b})^k`: the law enters only through the mass it places at
each level. -/
theorem exposureLaplace_natCast_eq_sum_exposureMass {n : ℕ} (law : FiniteReportLaw (Fin n))
    (exposure : Fin n → ℝ) (levels : Finset ℝ) (hlevels : ∀ index, exposure index ∈ levels)
    (scale : ℕ) :
    exposureLaplace law exposure scale =
      ∑ level ∈ levels, exposureMass law exposure level * Real.exp (-level) ^ scale := by
  unfold exposureLaplace FiniteReportLaw.expectation exposureMass
  rw [← Finset.sum_fiberwise_of_maps_to (fun index _ ↦ hlevels index)
    (fun index ↦ law.mass index * Real.exp (-((scale : ℝ) * exposure index)))]
  refine Finset.sum_congr rfl (fun level _ ↦ ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun index hindex ↦ ?_)
  rw [(Finset.mem_filter.mp hindex).2, ← Real.exp_nat_mul]
  congr 2
  ring

/-- NOTE1 section 6.3, identifiability for finite laws. Assumes: two finite exposure laws whose
transforms agree at every integer scale `0, 1, 2, …`. They then place the same mass at every
exposure level. The characters `k ↦ (e^{-b})^k` of the additive monoid of natural numbers are
distinct for distinct `b`, hence linearly independent (Dedekind), and the difference of the two
laws is a vanishing combination of them. -/
theorem exposureMass_eq_of_exposureLaplace_natCast_eq {n m : ℕ}
    (first : FiniteReportLaw (Fin n)) (firstExposure : Fin n → ℝ)
    (second : FiniteReportLaw (Fin m)) (secondExposure : Fin m → ℝ)
    (hlaplace : ∀ scale : ℕ,
      exposureLaplace first firstExposure scale = exposureLaplace second secondExposure scale)
    (level : ℝ) :
    exposureMass first firstExposure level = exposureMass second secondExposure level := by
  obtain ⟨levels, hfirst, hsecond, hlevel⟩ : ∃ levels : Finset ℝ,
      (∀ index, firstExposure index ∈ levels) ∧ (∀ index, secondExposure index ∈ levels) ∧
        level ∈ levels :=
    ⟨insert level (Finset.univ.image firstExposure ∪ Finset.univ.image secondExposure),
      fun index ↦ Finset.mem_insert_of_mem
        (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ index))),
      fun index ↦ Finset.mem_insert_of_mem
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ index))),
      Finset.mem_insert_self _ _⟩
  have hinjective : Function.Injective (fun point : ℝ ↦ powersHom ℝ (Real.exp (-point))) := by
    intro left right hsame
    have hexp := (powersHom ℝ).injective hsame
    simpa using hexp
  have hindependent := (linearIndependent_monoidHom (Multiplicative ℕ) ℝ).comp _ hinjective
  have hvanish : ∑ point ∈ levels,
      (exposureMass first firstExposure point - exposureMass second secondExposure point) •
        ((fun character : Multiplicative ℕ →* ℝ ↦ (character : Multiplicative ℕ → ℝ)) ∘
          fun point : ℝ ↦ powersHom ℝ (Real.exp (-point))) point = 0 := by
    funext scale
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
      powersHom_apply, Pi.zero_apply, sub_mul, Finset.sum_sub_distrib]
    rw [← exposureLaplace_natCast_eq_sum_exposureMass first firstExposure levels hfirst,
      ← exposureLaplace_natCast_eq_sum_exposureMass second secondExposure levels hsecond,
      hlaplace, sub_self]
  exact sub_eq_zero.mp
    (linearIndependent_iff'.mp hindependent levels _ hvanish level hlevel)

/-- NOTE1 section 6.3: knowing the transform at every scale `λ ≥ 0` determines a finite exposure
law. Assumes: two finite exposure laws whose transforms agree at every nonnegative scale. They
then place the same mass at every exposure level. -/
theorem exposureMass_eq_of_exposureLaplace_eq {n m : ℕ}
    (first : FiniteReportLaw (Fin n)) (firstExposure : Fin n → ℝ)
    (second : FiniteReportLaw (Fin m)) (secondExposure : Fin m → ℝ)
    (hlaplace : ∀ lam : ℝ, 0 ≤ lam →
      exposureLaplace first firstExposure lam = exposureLaplace second secondExposure lam)
    (level : ℝ) :
    exposureMass first firstExposure level = exposureMass second secondExposure level :=
  exposureMass_eq_of_exposureLaplace_natCast_eq first firstExposure second secondExposure
    (fun scale ↦ hlaplace scale (Nat.cast_nonneg scale)) level

open MeasureTheory

/-- NOTE1 (30) for an arbitrary exposure law: the transform `C(λ) = ∫ e^{-λ b} ν(db)` of a
measure `ν` on the line. -/
def measureLaplace (exposureLaw : Measure ℝ) (lam : ℝ) : ℝ :=
  ∫ exposure, Real.exp (-(lam * exposure)) ∂exposureLaw

/-- The measure carried by a finite exposure law: the point masses at its exposures, weighted by
the law. -/
def lawMeasure {n : ℕ} (law : FiniteReportLaw (Fin n)) (exposure : Fin n → ℝ) : Measure ℝ :=
  ∑ index, ENNReal.ofReal (law.mass index) • Measure.dirac (exposure index)

/-- Integrating against the measure of a finite law is taking the law's expectation of the
integrand at the exposures. -/
theorem integral_lawMeasure {n : ℕ} (law : FiniteReportLaw (Fin n)) (exposure : Fin n → ℝ)
    (integrand : ℝ → ℝ) :
    ∫ point, integrand point ∂lawMeasure law exposure =
      law.expectation (fun index ↦ integrand (exposure index)) := by
  unfold lawMeasure FiniteReportLaw.expectation
  rw [integral_finset_sum_measure]
  · refine Finset.sum_congr rfl (fun index _ ↦ ?_)
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (law.mass_nonneg index),
      smul_eq_mul]
  · intro index _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- The transform of the measure of a finite law is the finite transform `exposureLaplace`. -/
theorem measureLaplace_lawMeasure {n : ℕ} (law : FiniteReportLaw (Fin n))
    (exposure : Fin n → ℝ) (lam : ℝ) :
    measureLaplace (lawMeasure law exposure) lam = exposureLaplace law exposure lam :=
  integral_lawMeasure law exposure (fun point ↦ Real.exp (-(lam * point)))

/-- Assumes: a finite measure carried by `[0, R]`. Every continuous function is then integrable
against it, being bounded on `[0, R]`. -/
private theorem integrable_of_ae_mem_Icc (exposureLaw : Measure ℝ) [IsFiniteMeasure exposureLaw]
    (bound : ℝ) (hsupport : ∀ᵐ exposure ∂exposureLaw, exposure ∈ Set.Icc 0 bound)
    (integrand : ℝ → ℝ) (hcontinuous : Continuous integrand) :
    Integrable integrand exposureLaw := by
  obtain ⟨ceiling, hceiling⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) bound))
    |>.exists_bound_of_continuousOn hcontinuous.continuousOn
  exact Integrable.of_bound hcontinuous.aestronglyMeasurable ceiling
    (hsupport.mono fun exposure hexposure ↦ hceiling exposure hexposure)

/-- NOTE1 (36), lower bound, for an arbitrary probability measure. Assumes: the exposure law is
a probability measure carried by `[0, R]`. The transform is at least the survival factor at the
mean exposure: Jensen's inequality for the exponential. -/
theorem exp_neg_mean_le_measureLaplace (exposureLaw : Measure ℝ)
    [IsProbabilityMeasure exposureLaw] (bound lam : ℝ)
    (hsupport : ∀ᵐ exposure ∂exposureLaw, exposure ∈ Set.Icc 0 bound) :
    Real.exp (-(lam * ∫ exposure, exposure ∂exposureLaw)) ≤ measureLaplace exposureLaw lam := by
  have hlinear := integrable_of_ae_mem_Icc exposureLaw bound hsupport
    (fun exposure ↦ -(lam * exposure)) (by fun_prop)
  have hsurvival := integrable_of_ae_mem_Icc exposureLaw bound hsupport
    (fun exposure ↦ Real.exp (-(lam * exposure))) (by fun_prop)
  have hjensen := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ fun _ ↦ Set.mem_univ _) hlinear hsurvival
  rw [integral_neg, integral_const_mul] at hjensen
  exact hjensen

/-- NOTE1 (36), upper bound, for an arbitrary probability measure. Assumes: the exposure law is a
probability measure carried by `[0, R]` with `R > 0`. The transform is at most the endpoint chord
evaluated at the mean exposure. -/
theorem measureLaplace_le_chord (exposureLaw : Measure ℝ) [IsProbabilityMeasure exposureLaw]
    (bound lam : ℝ) (hbound : 0 < bound)
    (hsupport : ∀ᵐ exposure ∂exposureLaw, exposure ∈ Set.Icc 0 bound) :
    measureLaplace exposureLaw lam ≤
      1 - (∫ exposure, exposure ∂exposureLaw) / bound +
        (∫ exposure, exposure ∂exposureLaw) / bound * Real.exp (-(lam * bound)) := by
  have hne : bound ≠ 0 := ne_of_gt hbound
  have hidentity := integrable_of_ae_mem_Icc exposureLaw bound hsupport
    (fun exposure ↦ exposure) continuous_id
  have hsurvival := integrable_of_ae_mem_Icc exposureLaw bound hsupport
    (fun exposure ↦ Real.exp (-(lam * exposure))) (by fun_prop)
  have hmono : measureLaplace exposureLaw lam ≤ ∫ exposure,
      (1 + (Real.exp (-(lam * bound)) - 1) / bound * exposure) ∂exposureLaw := by
    refine integral_mono_ae hsurvival ((integrable_const 1).add (hidentity.const_mul _))
      (hsupport.mono fun exposure hexposure ↦ ?_)
    have hpoint := exp_chord_bound bound lam exposure hbound hexposure.1 hexposure.2
    have hrewrite : 1 - exposure / bound + exposure / bound * Real.exp (-(lam * bound)) =
        1 + (Real.exp (-(lam * bound)) - 1) / bound * exposure := by
      field_simp
      ring
    show Real.exp (-(lam * exposure)) ≤ 1 + (Real.exp (-(lam * bound)) - 1) / bound * exposure
    linarith [hpoint, hrewrite]
  rw [integral_add (integrable_const 1) (hidentity.const_mul _), integral_const,
    integral_const_mul, measureReal_univ_eq_one, smul_eq_mul, one_mul] at hmono
  have hrewrite :
      1 + (Real.exp (-(lam * bound)) - 1) / bound * ∫ exposure, exposure ∂exposureLaw =
        1 - (∫ exposure, exposure ∂exposureLaw) / bound +
          (∫ exposure, exposure ∂exposureLaw) / bound * Real.exp (-(lam * bound)) := by
    field_simp
    ring
  linarith [hmono, hrewrite]

/-- The lower bound of NOTE1 (36) is attained for measures: the point mass at a point has that
point as its mean and the survival factor there as its transform. -/
theorem measureLaplace_dirac (point lam : ℝ) :
    ∫ exposure, exposure ∂Measure.dirac point = point ∧
      measureLaplace (Measure.dirac point) lam = Real.exp (-(lam * point)) :=
  ⟨integral_dirac (fun exposure ↦ exposure) point,
    integral_dirac (fun exposure ↦ Real.exp (-(lam * exposure))) point⟩

/-- The upper bound of NOTE1 (36) is attained for measures: the endpoint mixture on `{0, R}`
with mean `b̄` has mean `b̄` and transform equal to the chord at `b̄`. -/
theorem measureLaplace_endpointMixture (bound mean lam : ℝ) (hlow : 0 ≤ mean)
    (hhigh : mean ≤ bound) (hbound : 0 < bound) :
    ∫ exposure, exposure ∂lawMeasure (endpointMixture bound mean hlow hhigh hbound)
        (endpointExposure bound) = mean ∧
      measureLaplace (lawMeasure (endpointMixture bound mean hlow hhigh hbound)
          (endpointExposure bound)) lam =
        1 - mean / bound + mean / bound * Real.exp (-(lam * bound)) :=
  ⟨(integral_lawMeasure _ _ (fun exposure ↦ exposure)).trans
      (expectation_endpointExposure bound mean hlow hhigh hbound),
    (measureLaplace_lawMeasure _ _ lam).trans
      (exposureLaplace_endpointMixture bound mean lam hlow hhigh hbound)⟩

/-- NOTE1 section 6.3 for measures: the squared transform is the transform of the convolution
`ν ∗ ν`, the law of the sum of two independent exposures drawn from `ν`. -/
theorem measureLaplace_conv (exposureLaw : Measure ℝ) [IsFiniteMeasure exposureLaw] (lam : ℝ) :
    measureLaplace (Measure.conv exposureLaw exposureLaw) lam =
      measureLaplace exposureLaw lam ^ 2 := by
  have hsplit : ∀ pair : ℝ × ℝ, Real.exp (-(lam * (pair.1 + pair.2))) =
      Real.exp (-(lam * pair.1)) * Real.exp (-(lam * pair.2)) := by
    intro pair
    rw [← Real.exp_add]
    congr 1
    ring
  unfold measureLaplace Measure.conv
  rw [integral_map (by fun_prop : Measurable fun pair : ℝ × ℝ ↦ pair.1 + pair.2).aemeasurable
    (by fun_prop : Continuous fun point : ℝ ↦ Real.exp (-(lam * point))).aestronglyMeasurable]
  simp only [hsplit]
  rw [integral_prod_mul (fun point ↦ Real.exp (-(lam * point)))
    (fun point ↦ Real.exp (-(lam * point))), pow_two]

/-- NOTE1 (35), log-convexity, for measures. Assumes: a finite measure carried by `[0, R]`. The
transform at a midpoint is dominated in square by the product of its endpoint values: the
quadratic `t ↦ ∫ (t e^{-λ b / 2} + e^{-μ b / 2})² ν(db)` is nonnegative, so its discriminant is
not positive. -/
theorem measureLaplace_sq_le_mul (exposureLaw : Measure ℝ) [IsFiniteMeasure exposureLaw]
    (bound lam mu : ℝ) (hsupport : ∀ᵐ exposure ∂exposureLaw, exposure ∈ Set.Icc 0 bound) :
    measureLaplace exposureLaw ((lam + mu) / 2) ^ 2 ≤
      measureLaplace exposureLaw lam * measureLaplace exposureLaw mu := by
  have hintegrable : ∀ scale : ℝ,
      Integrable (fun exposure ↦ Real.exp (-(scale * exposure))) exposureLaw :=
    fun scale ↦ integrable_of_ae_mem_Icc exposureLaw bound hsupport _ (by fun_prop)
  have hquadratic : ∀ t : ℝ, 0 ≤ measureLaplace exposureLaw lam * (t * t) +
      2 * measureLaplace exposureLaw ((lam + mu) / 2) * t + measureLaplace exposureLaw mu := by
    intro t
    have hpoint : ∀ exposure : ℝ,
        (t * Real.exp (-(lam * exposure) / 2) + Real.exp (-(mu * exposure) / 2)) ^ 2 =
          t * t * Real.exp (-(lam * exposure)) +
            2 * t * Real.exp (-((lam + mu) / 2 * exposure)) + Real.exp (-(mu * exposure)) := by
      intro exposure
      have hleft : Real.exp (-(lam * exposure) / 2) ^ 2 = Real.exp (-(lam * exposure)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      have hright : Real.exp (-(mu * exposure) / 2) ^ 2 = Real.exp (-(mu * exposure)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      have hcross : Real.exp (-(lam * exposure) / 2) * Real.exp (-(mu * exposure) / 2) =
          Real.exp (-((lam + mu) / 2 * exposure)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      linear_combination t * t * hleft + 2 * t * hcross + hright
    have hfirst : Integrable (fun exposure ↦ t * t * Real.exp (-(lam * exposure))) exposureLaw :=
      (hintegrable lam).const_mul (t * t)
    have hsecond : Integrable
        (fun exposure ↦ 2 * t * Real.exp (-((lam + mu) / 2 * exposure))) exposureLaw :=
      (hintegrable ((lam + mu) / 2)).const_mul (2 * t)
    have hsum : Integrable (fun exposure ↦ t * t * Real.exp (-(lam * exposure)) +
        2 * t * Real.exp (-((lam + mu) / 2 * exposure))) exposureLaw := hfirst.add hsecond
    have hvalue : ∫ exposure, (t * Real.exp (-(lam * exposure) / 2) +
        Real.exp (-(mu * exposure) / 2)) ^ 2 ∂exposureLaw =
        measureLaplace exposureLaw lam * (t * t) +
          2 * measureLaplace exposureLaw ((lam + mu) / 2) * t +
            measureLaplace exposureLaw mu := by
      rw [integral_congr_ae (ae_of_all _ hpoint), integral_add hsum (hintegrable mu),
        integral_add hfirst hsecond, integral_const_mul, integral_const_mul]
      unfold measureLaplace
      ring
    rw [← hvalue]
    exact integral_nonneg fun exposure ↦ sq_nonneg _
  have hdiscrim := discrim_le_zero hquadratic
  unfold discrim at hdiscrim
  nlinarith [hdiscrim]

/-- Assumes: a finite measure carried by `[0, R]`. The moment transform
`λ ↦ ∫ (-b)^k e^{-λ b} ν(db)` is differentiable with derivative the next moment transform; the
derivative passes under the integral because on `[0, R]` the differentiated integrand is bounded
uniformly for scales within distance one of `λ`. -/
theorem hasDerivAt_momentLaplace (exposureLaw : Measure ℝ) [IsFiniteMeasure exposureLaw]
    (bound : ℝ) (hsupport : ∀ᵐ exposure ∂exposureLaw, exposure ∈ Set.Icc 0 bound) (order : ℕ)
    (lam : ℝ) :
    HasDerivAt
      (fun scale ↦ ∫ exposure, (-exposure) ^ order * Real.exp (-(scale * exposure)) ∂exposureLaw)
      (∫ exposure, (-exposure) ^ (order + 1) * Real.exp (-(lam * exposure)) ∂exposureLaw)
      lam := by
  have hbound : ∀ᵐ exposure ∂exposureLaw, ∀ scale ∈ Metric.ball lam 1,
      ‖(-exposure) ^ (order + 1) * Real.exp (-(scale * exposure))‖ ≤
        bound ^ (order + 1) * Real.exp ((|lam| + 1) * bound) := by
    refine hsupport.mono fun exposure hexposure scale hscale ↦ ?_
    have hdist : |scale - lam| < 1 := by
      rw [← Real.dist_eq]
      exact Metric.mem_ball.mp hscale
    have hscaleabs : |scale| ≤ |lam| + 1 := by
      linarith [abs_sub_abs_le_abs_sub scale lam]
    have hpower : |(-exposure) ^ (order + 1)| ≤ bound ^ (order + 1) := by
      rw [abs_pow, abs_neg, abs_of_nonneg hexposure.1]
      exact pow_le_pow_left₀ hexposure.1 hexposure.2 _
    have hexponent : -(scale * exposure) ≤ (|lam| + 1) * bound := by
      nlinarith [neg_le_abs scale, abs_nonneg scale, hexposure.1, hexposure.2, hscaleabs]
    rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    exact mul_le_mul hpower (Real.exp_le_exp.mpr hexponent) (Real.exp_pos _).le
      ((abs_nonneg _).trans hpower)
  have hdiff : ∀ᵐ exposure ∂exposureLaw, ∀ scale ∈ Metric.ball lam 1,
      HasDerivAt (fun value ↦ (-exposure) ^ order * Real.exp (-(value * exposure)))
        ((-exposure) ^ (order + 1) * Real.exp (-(scale * exposure))) scale := by
    refine ae_of_all _ fun exposure scale _ ↦ ?_
    have hlinear : HasDerivAt (fun value : ℝ ↦ -(value * exposure)) (-exposure) scale := by
      have hstep := ((hasDerivAt_id scale).mul_const exposure).neg
      simpa using hstep
    refine (hlinear.exp.const_mul ((-exposure) ^ order)).congr_deriv ?_
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := exposureLaw) (x₀ := lam)
    (F := fun value exposure ↦ (-exposure) ^ order * Real.exp (-(value * exposure)))
    (F' := fun value exposure ↦ (-exposure) ^ (order + 1) * Real.exp (-(value * exposure)))
    zero_lt_one
    (Filter.Eventually.of_forall fun value ↦ (by fun_prop : Continuous fun exposure : ℝ ↦
      (-exposure) ^ order * Real.exp (-(value * exposure))).aestronglyMeasurable)
    (integrable_of_ae_mem_Icc exposureLaw bound hsupport _ (by fun_prop))
    ((by fun_prop : Continuous fun exposure : ℝ ↦
      (-exposure) ^ (order + 1) * Real.exp (-(lam * exposure))).aestronglyMeasurable)
    hbound (integrable_const _) hdiff).2

/-- NOTE1 (35) for measures. Assumes: a finite measure carried by `[0, R]`. Every iterated
derivative of the transform is the corresponding moment transform `∫ (-b)^k e^{-λ b} ν(db)`. -/
theorem iteratedDeriv_measureLaplace (exposureLaw : Measure ℝ) [IsFiniteMeasure exposureLaw]
    (bound : ℝ) (hsupport : ∀ᵐ exposure ∂exposureLaw, exposure ∈ Set.Icc 0 bound) (order : ℕ) :
    iteratedDeriv order (measureLaplace exposureLaw) =
      fun lam ↦ ∫ exposure, (-exposure) ^ order * Real.exp (-(lam * exposure)) ∂exposureLaw := by
  induction order with
  | zero =>
    funext lam
    simp [iteratedDeriv_zero, measureLaplace]
  | succ order ih =>
    rw [iteratedDeriv_succ, ih]
    funext lam
    exact (hasDerivAt_momentLaplace exposureLaw bound hsupport order lam).deriv

/-- NOTE1 (35), the sign pattern, for measures. Assumes: a finite measure carried by `[0, R]`.
The transform is completely monotone: `(-1)^k C^{(k)}(λ) = ∫ b^k e^{-λ b} ν(db) ≥ 0`. -/
theorem sign_iteratedDeriv_measureLaplace (exposureLaw : Measure ℝ)
    [IsFiniteMeasure exposureLaw] (bound : ℝ)
    (hsupport : ∀ᵐ exposure ∂exposureLaw, exposure ∈ Set.Icc 0 bound) (order : ℕ) (lam : ℝ) :
    0 ≤ (-1 : ℝ) ^ order * iteratedDeriv order (measureLaplace exposureLaw) lam := by
  rw [iteratedDeriv_measureLaplace exposureLaw bound hsupport order]
  show 0 ≤ (-1 : ℝ) ^ order *
    ∫ exposure, (-exposure) ^ order * Real.exp (-(lam * exposure)) ∂exposureLaw
  rw [← integral_const_mul]
  refine integral_nonneg_of_ae (hsupport.mono fun exposure hexposure ↦ ?_)
  have hpow : (-1 : ℝ) ^ order * (-exposure) ^ order = exposure ^ order := by
    rw [← mul_pow, show (-1 : ℝ) * -exposure = exposure from by ring]
  show 0 ≤ (-1 : ℝ) ^ order * ((-exposure) ^ order * Real.exp (-(lam * exposure)))
  rw [← mul_assoc, hpow]
  exact mul_nonneg (pow_nonneg hexposure.1 order) (Real.exp_pos _).le

/-- Assumes: a finite measure carried by `[0, R]`. A polynomial in the survival factor `e^{-b}`
integrates to the combination of transforms at integer scales with the polynomial's
coefficients: `∫ ∑ₖ cₖ e^{-k b} ν(db) = ∑ₖ cₖ C(k)`. -/
theorem integral_eval_exp_neg (exposureLaw : Measure ℝ) [IsFiniteMeasure exposureLaw]
    (bound : ℝ) (hsupport : ∀ᵐ exposure ∂exposureLaw, exposure ∈ Set.Icc 0 bound)
    (polynomial : Polynomial ℝ) :
    ∫ exposure, polynomial.eval (Real.exp (-exposure)) ∂exposureLaw =
      ∑ index ∈ Finset.range (polynomial.natDegree + 1),
        polynomial.coeff index * measureLaplace exposureLaw index := by
  have hintegrable : ∀ index ∈ Finset.range (polynomial.natDegree + 1),
      Integrable (fun exposure ↦ polynomial.coeff index * Real.exp (-exposure) ^ index)
        exposureLaw :=
    fun index _ ↦ integrable_of_ae_mem_Icc exposureLaw bound hsupport _ (by fun_prop)
  simp only [Polynomial.eval_eq_sum_range]
  rw [integral_finset_sum _ hintegrable]
  refine Finset.sum_congr rfl (fun index _ ↦ ?_)
  rw [integral_const_mul]
  unfold measureLaplace
  congr 1
  refine integral_congr_ae (ae_of_all _ fun exposure ↦ ?_)
  show Real.exp (-exposure) ^ index = Real.exp (-((index : ℝ) * exposure))
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- NOTE1 section 6.3, identifiability for exposure laws that are not finitely supported.
Assumes: two finite measures carried by `[0, R]` whose transforms agree at every integer scale.
Then the measures are equal. Every polynomial in `e^{-b}` has the same integral under both laws
(`integral_eval_exp_neg`); by Weierstrass on `[e^{-R}, 1]` every bounded continuous function is
within any `ε` of such a polynomial on `[0, R]`; and a finite measure is determined by its
integrals of bounded continuous functions. -/
theorem measure_eq_of_measureLaplace_natCast_eq (first second : Measure ℝ)
    [IsFiniteMeasure first] [IsFiniteMeasure second] (bound : ℝ)
    (hfirst : ∀ᵐ exposure ∂first, exposure ∈ Set.Icc 0 bound)
    (hsecond : ∀ᵐ exposure ∂second, exposure ∈ Set.Icc 0 bound)
    (hlaplace : ∀ scale : ℕ, measureLaplace first scale = measureLaplace second scale) :
    first = second := by
  have hmass : 0 < first.real Set.univ + second.real Set.univ + 1 := by
    have h1 : (0 : ℝ) ≤ first.real Set.univ := measureReal_nonneg
    have h2 : (0 : ℝ) ≤ second.real Set.univ := measureReal_nonneg
    linarith
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun bounded ↦ ?_
  have hclose : ∀ ε > 0,
      |∫ exposure, bounded exposure ∂first - ∫ exposure, bounded exposure ∂second| ≤ ε := by
    intro ε hε
    set tolerance := ε / (first.real Set.univ + second.real Set.univ + 1) with htolerance
    have hpositive : 0 < tolerance := div_pos hε hmass
    have hscale : tolerance * (first.real Set.univ + second.real Set.univ + 1) = ε :=
      div_mul_cancel₀ ε (ne_of_gt hmass)
    have hcontinuous : ContinuousOn (fun u ↦ bounded (-Real.log u))
        (Set.Icc (Real.exp (-bound)) 1) := by
      refine bounded.continuous.comp_continuousOn (Real.continuousOn_log.mono ?_).neg
      intro u hu
      exact ne_of_gt ((Real.exp_pos _).trans_le hu.1)
    obtain ⟨near, hnear⟩ :=
      exists_polynomial_near_of_continuousOn (Real.exp (-bound)) 1 _ hcontinuous _ hpositive
    have hpoint : ∀ law : Measure ℝ, (∀ᵐ exposure ∂law, exposure ∈ Set.Icc 0 bound) →
        ∀ᵐ exposure ∂law,
          ‖bounded exposure - near.eval (Real.exp (-exposure))‖ ≤ tolerance := by
      intro law hlaw
      refine hlaw.mono fun exposure hexposure ↦ ?_
      have hmem : Real.exp (-exposure) ∈ Set.Icc (Real.exp (-bound)) 1 :=
        Set.mem_Icc.mpr ⟨Real.exp_le_exp.mpr (by linarith [hexposure.2]),
          Real.exp_le_one_iff.mpr (by linarith [hexposure.1])⟩
      have hvalue := hnear _ hmem
      rw [Real.log_exp, neg_neg] at hvalue
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hvalue.le
    have hfirstbound := norm_integral_le_of_norm_le_const (hpoint first hfirst)
    have hsecondbound := norm_integral_le_of_norm_le_const (hpoint second hsecond)
    rw [integral_sub (bounded.integrable first) (integrable_of_ae_mem_Icc first bound hfirst
        (fun exposure ↦ near.eval (Real.exp (-exposure))) (by fun_prop)),
      Real.norm_eq_abs] at hfirstbound
    rw [integral_sub (bounded.integrable second) (integrable_of_ae_mem_Icc second bound hsecond
        (fun exposure ↦ near.eval (Real.exp (-exposure))) (by fun_prop)),
      Real.norm_eq_abs] at hsecondbound
    have hpolynomial : ∫ exposure, near.eval (Real.exp (-exposure)) ∂first =
        ∫ exposure, near.eval (Real.exp (-exposure)) ∂second := by
      rw [integral_eval_exp_neg first bound hfirst near,
        integral_eval_exp_neg second bound hsecond near]
      exact Finset.sum_congr rfl fun index _ ↦ by rw [hlaplace index]
    have htriangle := abs_sub
      (∫ exposure, bounded exposure ∂first - ∫ exposure, near.eval (Real.exp (-exposure)) ∂first)
      (∫ exposure, bounded exposure ∂second -
        ∫ exposure, near.eval (Real.exp (-exposure)) ∂second)
    rw [hpolynomial, sub_sub_sub_cancel_right] at htriangle
    rw [hpolynomial] at hfirstbound
    nlinarith [htriangle, hfirstbound, hsecondbound, hscale, hpositive,
      measureReal_nonneg (μ := first) (s := Set.univ),
      measureReal_nonneg (μ := second) (s := Set.univ)]
  have hzero :
      |∫ exposure, bounded exposure ∂first - ∫ exposure, bounded exposure ∂second| = 0 :=
    le_antisymm (le_of_forall_pos_le_add fun ε hε ↦ by linarith [hclose ε hε]) (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

/-- NOTE1 section 6.3: knowing the transform `C(λ)` for every `λ ≥ 0` determines the exposure
law. Assumes: two finite measures carried by `[0, R]` whose transforms agree at every
nonnegative scale. Then the measures are equal. -/
theorem measure_eq_of_measureLaplace_eq (first second : Measure ℝ)
    [IsFiniteMeasure first] [IsFiniteMeasure second] (bound : ℝ)
    (hfirst : ∀ᵐ exposure ∂first, exposure ∈ Set.Icc 0 bound)
    (hsecond : ∀ᵐ exposure ∂second, exposure ∈ Set.Icc 0 bound)
    (hlaplace : ∀ lam : ℝ, 0 ≤ lam → measureLaplace first lam = measureLaplace second lam) :
    first = second :=
  measure_eq_of_measureLaplace_natCast_eq first second bound hfirst hsecond
    fun scale ↦ hlaplace scale (Nat.cast_nonneg scale)

/-- Assumes: a finite measure carried by `[0, R]`. For every `k`, the `k`-th derivative of the
scaled moment transform `λ ↦ c ∫ (-b)^j e^{-λ b} ν(db)` is `c ∫ (-b)^(j+k) e^{-λ b} ν(db)`. -/
theorem iteratedDeriv_const_mul_momentLaplace (exposureLaw : Measure ℝ)
    [IsFiniteMeasure exposureLaw] (bound : ℝ)
    (hsupport : ∀ᵐ exposure ∂exposureLaw, exposure ∈ Set.Icc 0 bound) (factor : ℝ)
    (start order : ℕ) :
    iteratedDeriv order (fun lam ↦
        factor * ∫ exposure, (-exposure) ^ start * Real.exp (-(lam * exposure)) ∂exposureLaw) =
      fun lam ↦ factor *
        ∫ exposure, (-exposure) ^ (start + order) * Real.exp (-(lam * exposure))
          ∂exposureLaw := by
  induction order with
  | zero =>
    funext lam
    simp [iteratedDeriv_zero]
  | succ order ih =>
    rw [iteratedDeriv_succ, ih]
    funext lam
    rw [← add_assoc]
    exact ((hasDerivAt_momentLaplace exposureLaw bound hsupport (start + order) lam).const_mul
      factor).deriv

/-- NOTE1 section 6.3, the raw Brier curve. Assumes: a finite measure carried by `[0, R]` and
`h ≥ 0`. Under recombination scaling the Brier loss `2h(1 - C(λ))` of NOTE1 (31) has a completely
monotone derivative: `(-1)^k` times its `(k + 1)`-th derivative is nonnegative, so in particular
it increases with the multiplier `λ`. -/
theorem sign_iteratedDeriv_brierCurve (exposureLaw : Measure ℝ) [IsFiniteMeasure exposureLaw]
    (bound : ℝ) (hsupport : ∀ᵐ exposure ∂exposureLaw, exposure ∈ Set.Icc 0 bound) (h : ℝ)
    (hh : 0 ≤ h) (order : ℕ) (lam : ℝ) :
    0 ≤ (-1 : ℝ) ^ order *
      iteratedDeriv (order + 1) (fun scale ↦ 2 * h * (1 - measureLaplace exposureLaw scale))
        lam := by
  have hderiv : deriv (fun scale ↦ 2 * h * (1 - measureLaplace exposureLaw scale)) =
      fun scale ↦ -(2 * h) *
        ∫ exposure, (-exposure) ^ 1 * Real.exp (-(scale * exposure)) ∂exposureLaw := by
    funext scale
    have hbase := hasDerivAt_momentLaplace exposureLaw bound hsupport 0 scale
    simp only [pow_zero, one_mul, zero_add] at hbase
    exact ((hbase.const_sub 1).const_mul (2 * h)).deriv.trans (by ring)
  rw [iteratedDeriv_succ', hderiv,
    iteratedDeriv_const_mul_momentLaplace exposureLaw bound hsupport]
  show 0 ≤ (-1 : ℝ) ^ order * (-(2 * h) *
    ∫ exposure, (-exposure) ^ (1 + order) * Real.exp (-(lam * exposure)) ∂exposureLaw)
  have hintegral : 0 ≤ ∫ exposure, (-1 : ℝ) ^ (1 + order) *
      ((-exposure) ^ (1 + order) * Real.exp (-(lam * exposure))) ∂exposureLaw := by
    refine integral_nonneg_of_ae (hsupport.mono fun exposure hexposure ↦ ?_)
    show 0 ≤ (-1 : ℝ) ^ (1 + order) * ((-exposure) ^ (1 + order) * Real.exp (-(lam * exposure)))
    rw [← mul_assoc, ← mul_pow, show (-1 : ℝ) * -exposure = exposure from by ring]
    exact mul_nonneg (pow_nonneg hexposure.1 _) (Real.exp_pos _).le
  rw [integral_const_mul] at hintegral
  have hsign : (-1 : ℝ) ^ order * (-(2 * h) *
      ∫ exposure, (-exposure) ^ (1 + order) * Real.exp (-(lam * exposure)) ∂exposureLaw) =
        2 * h * ((-1 : ℝ) ^ (1 + order) *
          ∫ exposure, (-exposure) ^ (1 + order) * Real.exp (-(lam * exposure)) ∂exposureLaw) := by
    ring
  rw [hsign]
  exact mul_nonneg (mul_nonneg (by norm_num) hh) hintegral

/-- Assumes: a finite measure carried by `[0, R]`. Its self-convolution `ν ∗ ν`, the law of the
sum of two independent exposures, is carried by `[0, 2R]`. -/
theorem conv_ae_mem_Icc (exposureLaw : Measure ℝ) [IsFiniteMeasure exposureLaw] (bound : ℝ)
    (hsupport : ∀ᵐ exposure ∂exposureLaw, exposure ∈ Set.Icc 0 bound) :
    ∀ᵐ exposure ∂Measure.conv exposureLaw exposureLaw, exposure ∈ Set.Icc 0 (2 * bound) := by
  have hadd : Measurable fun pair : ℝ × ℝ ↦ pair.1 + pair.2 := by fun_prop
  unfold Measure.conv
  refine (ae_map_iff hadd.aemeasurable
    (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) (2 * bound)))).mpr ?_
  refine (Measure.ae_prod_iff_ae_ae
    (hadd (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) (2 * bound))))).mpr ?_
  refine hsupport.mono fun first hfirst ↦ hsupport.mono fun second hsecond ↦ ?_
  show first + second ∈ Set.Icc 0 (2 * bound)
  exact Set.mem_Icc.mpr ⟨by linarith [hfirst.1, hsecond.1], by linarith [hfirst.2, hsecond.2]⟩

/-- NOTE1 section 6.3, the repaired Brier curve. Assumes: a finite measure carried by `[0, R]`
and `h ≥ 0`. The population-optimal repaired Brier `h(1 - C(λ)²)` of NOTE1 (31) has a completely
monotone derivative, so it increases with the multiplier `λ`: `C²` is the transform of `ν ∗ ν`,
which is carried by `[0, 2R]`. -/
theorem sign_iteratedDeriv_repairedBrierCurve (exposureLaw : Measure ℝ)
    [IsFiniteMeasure exposureLaw] (bound : ℝ)
    (hsupport : ∀ᵐ exposure ∂exposureLaw, exposure ∈ Set.Icc 0 bound) (h : ℝ) (hh : 0 ≤ h)
    (order : ℕ) (lam : ℝ) :
    0 ≤ (-1 : ℝ) ^ order *
      iteratedDeriv (order + 1) (fun scale ↦ h * (1 - measureLaplace exposureLaw scale ^ 2))
        lam := by
  have hcurve : (fun scale ↦ h * (1 - measureLaplace exposureLaw scale ^ 2)) =
      fun scale ↦ 2 * (h / 2) *
        (1 - measureLaplace (Measure.conv exposureLaw exposureLaw) scale) := by
    funext scale
    rw [measureLaplace_conv]
    ring
  rw [hcurve]
  exact sign_iteratedDeriv_brierCurve (Measure.conv exposureLaw exposureLaw) (2 * bound)
    (conv_ae_mem_Icc exposureLaw bound hsupport) (h / 2) (by linarith) order lam

end

end Descent.Portability.ExposureLaplaceConstraints
