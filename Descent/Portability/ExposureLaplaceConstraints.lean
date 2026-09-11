/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ChronologyReportLaw
import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic

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
distinct for distinct `b`, hence linearly independent (Dedekind). So two finite laws whose
transforms agree at every integer scale, or at every scale `λ ≥ 0`, place the same mass at
every exposure level.

Not formalised: the general-measure versions. NOTE1 (35) and (36) are stated there for an
arbitrary probability measure on `[0, R]`, with differentiation under the integral sign and
the measure-theoretic Jensen inequality. The finite case is the one the pulse realisation of
NOTE1 section 6.3 and `FinitePulseExposure` actually uses, and no statement here assumes the
general case. Identifiability is likewise proved only for finite laws, and the remark that `m`
and `r` are not separately identified in calendar time is not formalised. Nothing here
identifies `ν` from data.

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

end

end Descent.Portability.ExposureLaplaceConstraints
