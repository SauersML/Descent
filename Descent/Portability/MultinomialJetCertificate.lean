/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MultinomialDriftStage
import Descent.Portability.TwoLocusMicroscopicKernel

assert_below Descent.Decision Descent.Program

/-!
# Polynomial certificates for the corpus diffusion jets

The multinomial drift stage of `MultinomialDriftStage` expands observables that are polynomials
of degree at most four in the resampled deme's haplotype frequencies, and its first-order term
is the second-order operator `resamplingOperator` of NOTE1 (10). The corpus observables are
`TwoLocusDiffusionJet`s, whose drift `driftAt` is defined by the jet algebra instead. This module
supplies the certificate that ties the two: `JetPolynomialCertificate jet` gives, for every deme
and state, a polynomial in that deme's four haplotype frequencies whose coefficients depend
only on the other demes, which reproduces the jet's value, its gradient `gradientAt` as the
formal partial derivatives, and its drift `driftAt` as `resamplingOperator`, with explicit bounds
on the total degree and on the coefficient mass.

`coefficientMass p` is the sum of the absolute coefficients of `p`. It is subadditive
(`coefficientMass_add_le`), homogeneous (`coefficientMass_smul`) and submultiplicative
(`coefficientMass_mul_le`, by expanding both factors into monomials), so a certificate's mass
bound propagates through the jet algebra. `totalStirlingWeight_le` bounds the Stirling weight of
a multi-index of degree at most four by `24`, through the Bell numbers and `∏ b_a! ≤ (Σ b_a)!`,
so `sum_coeff_remainder_le` turns the remainder constant of (10) into `107` times the coefficient
mass.

The certificate is closed under the corpus jet algebra: `JetPolynomialCertificate.const`,
`JetPolynomialCertificate.add` and `JetPolynomialCertificate.smul` certify the constant jet, sums
and scalar multiples, adding degrees by maximum and masses by sum. `JetPolynomialCertificate.mul`
certifies products, adding degrees and multiplying masses. Its drift rests on
`resamplingOperator_mul`, the product rule of the second-order operator `p L q + q L p` plus the
carré du champ `Σ_{a,c} (x_a δ_ac - x_a x_c) ∂_a p ∂_c q`, and on
`twoLocusHaplotypeCovariance_eq_sum`, which identifies that carré du champ with the corpus
multinomial covariance of the two gradients that `TwoLocusDiffusionJet.mul` adds.

The base jets are certified directly. `JetPolynomialCertificate.leftFrequency` and
`JetPolynomialCertificate.rightFrequency` are the linear polynomials `X_AB + X_Ab` and
`X_AB + X_aB` in their own deme and constants elsewhere; `JetPolynomialCertificate.linkage` is the
determinant `X_AB X_ab - X_Ab X_aB`, whose second-order operator is `-D` by
`resamplingOperator_X_mul_X`, matching the corpus `twoLocusLinkageDrift_eq_neg_linkage`.

The corpus coordinate jets are built from these by the jet algebra, so their certificates are
too: `JetPolynomialCertificate.heterozygosity`, `rightHeterozygosity`, `linkageProduct`,
`dzObservable` and `jointHeterozygosity`, collected by `JetPolynomialCertificate.enlarged` over the
enlarged coordinates of NOTE1 (6). Every one has total degree at most four
(`JetPolynomialCertificate.enlarged_degree_le`), so `enlargedObservable` presents each enlarged
coordinate as a `MultinomialDriftStage.DegreeFourObservable` in any resampled deme, with its drift
bound read off the corpus resampling certificate. `apply_multinomialDriftStage_enlarged` is the
consequence for NOTE1 §2.3: one multinomial drift stage at rate `rate` and step `step` moves every
enlarged coordinate by `step · rate · driftAt`, up to a slack of order `step`.

What is NOT proved in this module: the multinomial microscopic approximation assembled from these
stages; its branch type depends on the step size, which the corpus `MicroscopicApproximation`
does not allow.

## Empirical status

None. The bodies here are algebra: coefficients of polynomials, their absolute sums and the
evaluation of formal derivatives. No measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MultinomialJetCertificate

open Coalescent SimplexResamplingKernel
open Descent.Portability.MultinomialMomentExpansion
open Descent.Portability.MultinomialDriftStage

noncomputable section

/-! ## Coefficient mass -/

/-- The coefficient mass of a polynomial: the sum of the absolute values of its coefficients. -/
def coefficientMass {H : Type*} (p : MvPolynomial H ℝ) : ℝ :=
  ∑ s ∈ p.support, |p.coeff s|

/-- The coefficient mass is nonnegative. -/
theorem coefficientMass_nonneg {H : Type*} (p : MvPolynomial H ℝ) : 0 ≤ coefficientMass p :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- The coefficient mass may be summed over any finite set of exponents containing the
support. -/
theorem coefficientMass_eq_sum_of_subset {H : Type*} (p : MvPolynomial H ℝ)
    {S : Finset (H →₀ ℕ)} (hS : p.support ⊆ S) : coefficientMass p = ∑ s ∈ S, |p.coeff s| := by
  refine Finset.sum_subset hS fun s _ hs ↦ ?_
  rw [MvPolynomial.notMem_support_iff.mp hs, abs_zero]

/-- The coefficient mass is subadditive. -/
theorem coefficientMass_add_le {H : Type*} [DecidableEq H] (p q : MvPolynomial H ℝ) :
    coefficientMass (p + q) ≤ coefficientMass p + coefficientMass q := by
  rw [coefficientMass_eq_sum_of_subset (p + q) MvPolynomial.support_add,
    coefficientMass_eq_sum_of_subset p
      (Finset.subset_union_left : p.support ⊆ p.support ∪ q.support),
    coefficientMass_eq_sum_of_subset q
      (Finset.subset_union_right : q.support ⊆ p.support ∪ q.support),
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  rw [MvPolynomial.coeff_add]
  exact abs_add_le _ _

/-- Scaling a polynomial scales its coefficient mass by the absolute value of the scalar. -/
theorem coefficientMass_smul {H : Type*} (r : ℝ) (p : MvPolynomial H ℝ) :
    coefficientMass (r • p) = |r| * coefficientMass p := by
  rw [coefficientMass_eq_sum_of_subset (r • p) MvPolynomial.support_smul, coefficientMass,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, abs_mul]

/-- A monomial has coefficient mass the absolute value of its coefficient. -/
theorem coefficientMass_monomial {H : Type*} (s : H →₀ ℕ) (c : ℝ) :
    coefficientMass (MvPolynomial.monomial s c) = |c| := by
  classical
  rw [coefficientMass_eq_sum_of_subset _ MvPolynomial.support_monomial_subset,
    Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

/-- The coefficient mass of a finite sum is at most the sum of the coefficient masses. -/
theorem coefficientMass_sum_le {H ι : Type*} [DecidableEq H] (S : Finset ι)
    (f : ι → MvPolynomial H ℝ) :
    coefficientMass (∑ i ∈ S, f i) ≤ ∑ i ∈ S, coefficientMass (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [coefficientMass]
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (coefficientMass_add_le _ _).trans (add_le_add_left ih _)

/-- The coefficient mass is submultiplicative: expanding both factors into monomials, the
product is a double sum of monomials whose coefficients are products. -/
theorem coefficientMass_mul_le {H : Type*} [DecidableEq H] (p q : MvPolynomial H ℝ) :
    coefficientMass (p * q) ≤ coefficientMass p * coefficientMass q := by
  have hprod : p * q = ∑ s ∈ p.support, ∑ t ∈ q.support,
      MvPolynomial.monomial (s + t) (p.coeff s * q.coeff t) := by
    conv_lhs => rw [MvPolynomial.as_sum p, MvPolynomial.as_sum q]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun t _ ↦
      MvPolynomial.monomial_mul
  rw [hprod]
  calc coefficientMass (∑ s ∈ p.support, ∑ t ∈ q.support,
          MvPolynomial.monomial (s + t) (p.coeff s * q.coeff t))
      ≤ ∑ s ∈ p.support, coefficientMass (∑ t ∈ q.support,
          MvPolynomial.monomial (s + t) (p.coeff s * q.coeff t)) :=
        coefficientMass_sum_le _ _
    _ ≤ ∑ s ∈ p.support, ∑ t ∈ q.support,
          coefficientMass (MvPolynomial.monomial (s + t) (p.coeff s * q.coeff t)) :=
        Finset.sum_le_sum fun s _ ↦ coefficientMass_sum_le _ _
    _ = coefficientMass p * coefficientMass q := by
        simp only [coefficientMass_monomial, abs_mul]
        rw [coefficientMass, coefficientMass, Finset.sum_mul_sum]

/-! ## The remainder constant of (10) -/

/-- The total Stirling weight below `b` is the product over categories of the Bell numbers
`Σ_i S(b_a, i)`. -/
theorem totalStirlingWeight_eq_prod {H : Type*} [Fintype H] [DecidableEq H] (b : H → ℕ) :
    totalStirlingWeight b
      = ∏ a, ∑ i ∈ Finset.range (b a + 1), (Nat.stirlingSecond (b a) i : ℝ) :=
  (Finset.prod_univ_sum (fun a ↦ Finset.range (b a + 1))
    (fun a i ↦ (Nat.stirlingSecond (b a) i : ℝ))).symm

/-- For a multi-index of degree at most four the total Stirling weight is at most `24`: each
Bell number of order at most four is at most the factorial, and `∏_a b_a! ≤ (Σ_a b_a)!`. -/
theorem totalStirlingWeight_le {H : Type*} [Fintype H] [DecidableEq H] (b : H → ℕ)
    (hb : ∑ a, b a ≤ 4) : totalStirlingWeight b ≤ 24 := by
  have hbell : ∀ k, k ≤ 4 → ∑ i ∈ Finset.range (k + 1), Nat.stirlingSecond k i ≤ k.factorial := by
    intro k hk
    interval_cases k <;> simp [Finset.sum_range_succ, Nat.stirlingSecond, Nat.factorial]
  have hle : ∀ a, b a ≤ 4 := fun a ↦
    (Finset.single_le_sum (fun c _ ↦ Nat.zero_le (b c)) (Finset.mem_univ a)).trans hb
  have hprodle : ∏ a, ∑ i ∈ Finset.range (b a + 1), Nat.stirlingSecond (b a) i
      ≤ ∏ a, (b a).factorial :=
    Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) fun a _ ↦ hbell (b a) (hle a)
  have hmulti : ∏ a, (b a).factorial ≤ (∑ a, b a).factorial :=
    calc ∏ a, (b a).factorial
        ≤ (∏ a, (b a).factorial) * Nat.multinomial Finset.univ b :=
          Nat.le_mul_of_pos_right _ (Nat.multinomial_pos Finset.univ b)
      _ = (∑ a, b a).factorial := Nat.multinomial_spec Finset.univ b
  have hfact : (∑ a, b a).factorial ≤ 24 := (Nat.factorial_le hb).trans (by decide)
  have hnat : ∏ a, ∑ i ∈ Finset.range (b a + 1), Nat.stirlingSecond (b a) i ≤ 24 :=
    hprodle.trans (hmulti.trans hfact)
  rw [totalStirlingWeight_eq_prod]
  exact_mod_cast hnat

/-- The remainder constant of (10) on a polynomial of total degree at most four is at most
`107` times its coefficient mass. -/
theorem sum_coeff_remainder_le {H : Type*} [Fintype H] [DecidableEq H] (p : MvPolynomial H ℝ)
    (hp : p.totalDegree ≤ 4) :
    ∑ s ∈ p.support, |p.coeff s| * (11 + 4 * totalStirlingWeight ⇑s)
      ≤ 107 * coefficientMass p := by
  rw [coefficientMass, Finset.mul_sum]
  refine Finset.sum_le_sum fun s hs ↦ ?_
  have hdeg : ∑ a, s a ≤ 4 := by
    have hdegree := MvPolynomial.le_totalDegree hs
    rw [Finsupp.sum_fintype s (fun _ e ↦ e) (fun _ ↦ rfl)] at hdegree
    omega
  have hweight := totalStirlingWeight_le (⇑s) hdeg
  nlinarith [abs_nonneg (p.coeff s)]

/-! ## The product rule of the second-order operator -/

/-- The coefficient `x_a δ_ac - x_a x_c` of the second-order operator is symmetric. -/
theorem resamplingCoefficient_symm {H : Type*} [DecidableEq H] (x : H → ℝ) (a c : H) :
    (if c = a then x c else 0) - x c * x a = (if a = c then x a else 0) - x a * x c := by
  by_cases hac : a = c
  · subst hac
    rfl
  · rw [if_neg (Ne.symm hac), if_neg hac, mul_comm]

/-- **The product rule of the second-order operator of (10).** On a product the operator is
`p L q + q L p` plus the carré du champ `Σ_{a,c} (x_a δ_ac - x_a x_c) ∂_a p ∂_c q`. -/
theorem resamplingOperator_mul {H : Type*} [Fintype H] [DecidableEq H] (x : H → ℝ)
    (p q : MvPolynomial H ℝ) :
    resamplingOperator x (p * q)
      = MvPolynomial.eval x p * resamplingOperator x q
        + MvPolynomial.eval x q * resamplingOperator x p
        + ∑ a, ∑ c, ((if a = c then x a else 0) - x a * x c)
            * (MvPolynomial.eval x (MvPolynomial.pderiv a p)
              * MvPolynomial.eval x (MvPolynomial.pderiv c q)) := by
  have hpoint : ∀ a c,
      MvPolynomial.eval x (MvPolynomial.pderiv a (MvPolynomial.pderiv c (p * q)))
        = MvPolynomial.eval x (MvPolynomial.pderiv a (MvPolynomial.pderiv c p))
            * MvPolynomial.eval x q
          + MvPolynomial.eval x (MvPolynomial.pderiv c p)
            * MvPolynomial.eval x (MvPolynomial.pderiv a q)
          + MvPolynomial.eval x (MvPolynomial.pderiv a p)
            * MvPolynomial.eval x (MvPolynomial.pderiv c q)
          + MvPolynomial.eval x p
            * MvPolynomial.eval x (MvPolynomial.pderiv a (MvPolynomial.pderiv c q)) := by
    intro a c
    rw [MvPolynomial.pderiv_mul, map_add, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul]
    simp only [map_add, map_mul]
    ring
  have hswap : ∑ a, ∑ c, ((if a = c then x a else 0) - x a * x c)
        * (MvPolynomial.eval x (MvPolynomial.pderiv c p)
          * MvPolynomial.eval x (MvPolynomial.pderiv a q))
      = ∑ a, ∑ c, ((if a = c then x a else 0) - x a * x c)
        * (MvPolynomial.eval x (MvPolynomial.pderiv a p)
          * MvPolynomial.eval x (MvPolynomial.pderiv c q)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
    rw [resamplingCoefficient_symm]
  have hsplit : ∀ a c, ((if a = c then x a else 0) - x a * x c)
        * (MvPolynomial.eval x (MvPolynomial.pderiv a (MvPolynomial.pderiv c p))
            * MvPolynomial.eval x q
          + MvPolynomial.eval x (MvPolynomial.pderiv c p)
            * MvPolynomial.eval x (MvPolynomial.pderiv a q)
          + MvPolynomial.eval x (MvPolynomial.pderiv a p)
            * MvPolynomial.eval x (MvPolynomial.pderiv c q)
          + MvPolynomial.eval x p
            * MvPolynomial.eval x (MvPolynomial.pderiv a (MvPolynomial.pderiv c q)))
      = MvPolynomial.eval x q * (((if a = c then x a else 0) - x a * x c)
          * MvPolynomial.eval x (MvPolynomial.pderiv a (MvPolynomial.pderiv c p)))
        + ((if a = c then x a else 0) - x a * x c)
          * (MvPolynomial.eval x (MvPolynomial.pderiv c p)
            * MvPolynomial.eval x (MvPolynomial.pderiv a q))
        + ((if a = c then x a else 0) - x a * x c)
          * (MvPolynomial.eval x (MvPolynomial.pderiv a p)
            * MvPolynomial.eval x (MvPolynomial.pderiv c q))
        + MvPolynomial.eval x p * (((if a = c then x a else 0) - x a * x c)
          * MvPolynomial.eval x (MvPolynomial.pderiv a (MvPolynomial.pderiv c q))) := by
    intro a c
    ring
  simp only [resamplingOperator, hpoint, hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hswap]
  ring

/-- The corpus multinomial covariance of two haplotype scores is the carré du champ form
`Σ_{a,c} (x_a δ_ac - x_a x_c) u_a v_c` at the deme's haplotype frequencies. -/
theorem twoLocusHaplotypeCovariance_eq_sum (frequency : TwoLocusHaplotypeFrequencies)
    (first second : TwoLocusHaplotype → ℝ) :
    twoLocusHaplotypeCovariance frequency first second
      = ∑ a, ∑ c, ((if a = c then haplotypeCoordinate frequency a else 0)
          - haplotypeCoordinate frequency a * haplotypeCoordinate frequency c)
          * (first a * second c) := by
  simp only [RandomStageKernel.sum_haplotype, twoLocusHaplotypeCovariance, twoLocusHaplotypeMean,
    haplotypeCoordinate, eq_self_iff_true, if_true, if_false, reduceCtorEq]
  ring

/-- The second-order operator of (10) on a product of two coordinates is the coefficient
`x_a δ_ab - x_a x_b`. -/
theorem resamplingOperator_X_mul_X {H : Type*} [Fintype H] [DecidableEq H] (x : H → ℝ)
    (a b : H) :
    resamplingOperator x (MvPolynomial.X a * MvPolynomial.X b)
      = (if a = b then x a else 0) - x a * x b := by
  simp [resamplingOperator_mul, resamplingOperator_X, MvPolynomial.pderiv_X, Pi.single_apply,
    apply_ite, Finset.sum_ite_eq, ite_mul, mul_ite]

/-! ## Certificates and their algebra -/

/-- **A polynomial certificate for a corpus diffusion jet.** For every deme and state, a
polynomial in that deme's four haplotype frequencies whose coefficients depend only on the other
demes reproduces the jet's value, its gradient as formal partial derivatives and its drift as
the second-order operator of NOTE1 (10), with a uniform bound on the total degree and on the
coefficient mass.
Assumes: the six Prop fields. `JetPolynomialCertificate.const` is a concrete inhabitant. -/
structure JetPolynomialCertificate {D : ℕ} (jet : TwoLocusDiffusionJet D) where
  /-- The polynomial in the named deme, with coefficients read off the other demes. -/
  polynomial : Fin D → (Fin D → TwoLocusHaplotypeFrequencies) →
    MvPolynomial TwoLocusHaplotype ℝ
  /-- A uniform bound on the total degree. -/
  degree : ℕ
  /-- The polynomial has total degree at most `degree`. -/
  totalDegree_le : ∀ deme state, (polynomial deme state).totalDegree ≤ degree
  /-- A uniform bound on the coefficient mass. -/
  massBound : ℝ
  /-- The coefficient mass is at most `massBound`. -/
  mass_le : ∀ deme state, coefficientMass (polynomial deme state) ≤ massBound
  /-- The coefficients do not depend on the named deme's frequencies. -/
  polynomial_update : ∀ deme state frequency,
    polynomial deme (Function.update state deme frequency) = polynomial deme state
  /-- The jet's value is the polynomial evaluated at the named deme's frequencies. -/
  value_eq : ∀ deme state,
    jet.value state = MvPolynomial.eval (haplotypeCoordinate (state deme)) (polynomial deme state)
  /-- The jet's gradient in the named deme is the formal partial derivative. -/
  gradient_eq : ∀ deme state observed,
    jet.gradientAt deme state observed = MvPolynomial.eval (haplotypeCoordinate (state deme))
      (MvPolynomial.pderiv observed (polynomial deme state))
  /-- The jet's drift in the named deme is the second-order operator of (10). -/
  drift_eq : ∀ deme state,
    jet.driftAt deme state
      = resamplingOperator (haplotypeCoordinate (state deme)) (polynomial deme state)

namespace JetPolynomialCertificate

/-- The constant jet is certified by the constant polynomial. -/
def const {D : ℕ} (constant : ℝ) :
    JetPolynomialCertificate (TwoLocusDiffusionJet.const (D := D) constant) where
  polynomial _ _ := MvPolynomial.C constant
  degree := 0
  totalDegree_le _ _ := (MvPolynomial.totalDegree_C constant).le
  massBound := |constant|
  mass_le _ _ := le_of_eq (by rw [MvPolynomial.C_apply, coefficientMass_monomial])
  polynomial_update _ _ _ := by dsimp only
  value_eq _ _ := (MvPolynomial.eval_C constant).symm
  gradient_eq _ _ _ := by simp [TwoLocusDiffusionJet.const, MvPolynomial.pderiv_C]
  drift_eq _ _ := by simp [TwoLocusDiffusionJet.const, resamplingOperator, MvPolynomial.pderiv_C]

/-- A sum of certified jets is certified by the sum of the polynomials. -/
def add {D : ℕ} {first second : TwoLocusDiffusionJet D}
    (hfirst : JetPolynomialCertificate first) (hsecond : JetPolynomialCertificate second) :
    JetPolynomialCertificate (first.add second) where
  polynomial deme state := hfirst.polynomial deme state + hsecond.polynomial deme state
  degree := max hfirst.degree hsecond.degree
  totalDegree_le deme state := (MvPolynomial.totalDegree_add _ _).trans
    (max_le_max (hfirst.totalDegree_le deme state) (hsecond.totalDegree_le deme state))
  massBound := hfirst.massBound + hsecond.massBound
  mass_le deme state := (coefficientMass_add_le _ _).trans
    (add_le_add (hfirst.mass_le deme state) (hsecond.mass_le deme state))
  polynomial_update deme state frequency := by
    simp only [hfirst.polynomial_update, hsecond.polynomial_update]
  value_eq deme state := by
    simp only [TwoLocusDiffusionJet.add, map_add, hfirst.value_eq deme state,
      hsecond.value_eq deme state]
  gradient_eq deme state observed := by
    simp only [TwoLocusDiffusionJet.add, map_add, hfirst.gradient_eq deme state observed,
      hsecond.gradient_eq deme state observed]
  drift_eq deme state := by
    simp only [TwoLocusDiffusionJet.add, resamplingOperator_add, hfirst.drift_eq deme state,
      hsecond.drift_eq deme state]

/-- Evaluation of a scalar multiple of a polynomial. -/
theorem eval_smul {H : Type*} (x : H → ℝ) (r : ℝ) (p : MvPolynomial H ℝ) :
    MvPolynomial.eval x (r • p) = r * MvPolynomial.eval x p := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]

/-- A scalar multiple of a certified jet is certified by the scalar multiple of the
polynomial. -/
def smul {D : ℕ} {observable : TwoLocusDiffusionJet D} (scalar : ℝ)
    (hobservable : JetPolynomialCertificate observable) :
    JetPolynomialCertificate (TwoLocusDiffusionJet.smul scalar observable) where
  polynomial deme state := scalar • hobservable.polynomial deme state
  degree := hobservable.degree
  totalDegree_le deme state := (MvPolynomial.totalDegree_smul_le scalar _).trans
    (hobservable.totalDegree_le deme state)
  massBound := |scalar| * hobservable.massBound
  mass_le deme state := by
    rw [coefficientMass_smul]
    exact mul_le_mul_of_nonneg_left (hobservable.mass_le deme state) (abs_nonneg _)
  polynomial_update deme state frequency := by
    simp only [hobservable.polynomial_update]
  value_eq deme state := by
    simp only [TwoLocusDiffusionJet.smul, eval_smul, hobservable.value_eq deme state]
  gradient_eq deme state observed := by
    simp only [TwoLocusDiffusionJet.smul, Derivation.map_smul, eval_smul,
      hobservable.gradient_eq deme state observed]
  drift_eq deme state := by
    simp only [TwoLocusDiffusionJet.smul, resamplingOperator_smul,
      hobservable.drift_eq deme state]

/-- A product of certified jets is certified by the product of the polynomials: the gradient
follows the Leibniz rule, and the drift follows the product rule of the second-order operator,
whose carré du champ is the corpus multinomial covariance of the two gradients. -/
def mul {D : ℕ} {first second : TwoLocusDiffusionJet D}
    (hfirst : JetPolynomialCertificate first) (hsecond : JetPolynomialCertificate second) :
    JetPolynomialCertificate (first.mul second) where
  polynomial deme state := hfirst.polynomial deme state * hsecond.polynomial deme state
  degree := hfirst.degree + hsecond.degree
  totalDegree_le deme state := (MvPolynomial.totalDegree_mul _ _).trans
    (add_le_add (hfirst.totalDegree_le deme state) (hsecond.totalDegree_le deme state))
  massBound := hfirst.massBound * hsecond.massBound
  mass_le deme state := (coefficientMass_mul_le _ _).trans
    (mul_le_mul (hfirst.mass_le deme state) (hsecond.mass_le deme state)
      (coefficientMass_nonneg _) ((coefficientMass_nonneg _).trans (hfirst.mass_le deme state)))
  polynomial_update deme state frequency := by
    simp only [hfirst.polynomial_update, hsecond.polynomial_update]
  value_eq deme state := by
    simp only [TwoLocusDiffusionJet.mul, map_mul, hfirst.value_eq deme state,
      hsecond.value_eq deme state]
  gradient_eq deme state observed := by
    simp only [TwoLocusDiffusionJet.mul, MvPolynomial.pderiv_mul, map_add, map_mul,
      hfirst.value_eq deme state, hsecond.value_eq deme state,
      hfirst.gradient_eq deme state observed, hsecond.gradient_eq deme state observed]
    ring
  drift_eq deme state := by
    simp only [TwoLocusDiffusionJet.mul, resamplingOperator_mul,
      twoLocusHaplotypeCovariance_eq_sum, hfirst.value_eq deme state,
      hsecond.value_eq deme state, hfirst.drift_eq deme state, hsecond.drift_eq deme state,
      hfirst.gradient_eq deme state, hsecond.gradient_eq deme state]
    try ring

/-- The left marginal frequency of deme `index` is certified: in its own deme it is the linear
polynomial `X_AB + X_Ab`, in any other deme a constant. -/
def leftFrequency {D : ℕ} (index : Fin D) :
    JetPolynomialCertificate (twoLocusLeftFrequencyJet index) where
  polynomial deme state := if deme = index then MvPolynomial.X .AB + MvPolynomial.X .Ab
    else MvPolynomial.C (state index).leftFrequency
  degree := 1
  totalDegree_le deme state := by
    split_ifs
    · exact (MvPolynomial.totalDegree_add _ _).trans (by simp [MvPolynomial.totalDegree_X])
    · simp [MvPolynomial.totalDegree_C]
  massBound := 2
  mass_le deme state := by
    split_ifs
    · refine (coefficientMass_add_le _ _).trans ?_
      simp [MvPolynomial.X, coefficientMass_monomial]
      norm_num
    · rw [MvPolynomial.C_apply, coefficientMass_monomial,
        abs_of_nonneg (state index).leftFrequency_nonneg]
      linarith [(state index).leftFrequency_le_one]
  polynomial_update deme state frequency := by
    by_cases hdeme : deme = index
    · simp only [if_pos hdeme]
    · simp only [if_neg hdeme, Function.update_of_ne (Ne.symm hdeme)]
  value_eq deme state := by
    by_cases hdeme : deme = index
    · subst hdeme
      simp [twoLocusLeftFrequencyJet, TwoLocusHaplotypeFrequencies.leftFrequency,
        haplotypeCoordinate]
    · rw [if_neg hdeme]
      exact (MvPolynomial.eval_C _).symm
  gradient_eq deme state observed := by
    by_cases hdeme : deme = index
    · subst hdeme
      cases observed <;>
        simp [twoLocusLeftFrequencyJet, twoLocusLeftAlleleIndicator, MvPolynomial.pderiv_X,
          Pi.single_apply]
    · simp [twoLocusLeftFrequencyJet, hdeme, MvPolynomial.pderiv_C]
  drift_eq deme state := by
    by_cases hdeme : deme = index
    · subst hdeme
      simp [twoLocusLeftFrequencyJet, resamplingOperator_add, resamplingOperator_X]
    · simp [twoLocusLeftFrequencyJet, hdeme, resamplingOperator, MvPolynomial.pderiv_C]

/-- The right marginal frequency of deme `index` is certified: in its own deme it is the linear
polynomial `X_AB + X_aB`, in any other deme a constant. -/
def rightFrequency {D : ℕ} (index : Fin D) :
    JetPolynomialCertificate (twoLocusRightFrequencyJet index) where
  polynomial deme state := if deme = index then MvPolynomial.X .AB + MvPolynomial.X .aB
    else MvPolynomial.C (state index).rightFrequency
  degree := 1
  totalDegree_le deme state := by
    split_ifs
    · exact (MvPolynomial.totalDegree_add _ _).trans (by simp [MvPolynomial.totalDegree_X])
    · simp [MvPolynomial.totalDegree_C]
  massBound := 2
  mass_le deme state := by
    split_ifs
    · refine (coefficientMass_add_le _ _).trans ?_
      simp [MvPolynomial.X, coefficientMass_monomial]
      norm_num
    · rw [MvPolynomial.C_apply, coefficientMass_monomial,
        abs_of_nonneg (state index).rightFrequency_nonneg]
      linarith [(state index).rightFrequency_le_one]
  polynomial_update deme state frequency := by
    by_cases hdeme : deme = index
    · simp only [if_pos hdeme]
    · simp only [if_neg hdeme, Function.update_of_ne (Ne.symm hdeme)]
  value_eq deme state := by
    by_cases hdeme : deme = index
    · subst hdeme
      simp [twoLocusRightFrequencyJet, TwoLocusHaplotypeFrequencies.rightFrequency,
        haplotypeCoordinate]
    · rw [if_neg hdeme]
      exact (MvPolynomial.eval_C _).symm
  gradient_eq deme state observed := by
    by_cases hdeme : deme = index
    · subst hdeme
      cases observed <;>
        simp [twoLocusRightFrequencyJet, twoLocusRightAlleleIndicator, MvPolynomial.pderiv_X,
          Pi.single_apply]
    · simp [twoLocusRightFrequencyJet, hdeme, MvPolynomial.pderiv_C]
  drift_eq deme state := by
    by_cases hdeme : deme = index
    · subst hdeme
      simp [twoLocusRightFrequencyJet, resamplingOperator_add, resamplingOperator_X]
    · simp [twoLocusRightFrequencyJet, hdeme, resamplingOperator, MvPolynomial.pderiv_C]

/-- The linkage determinant of deme `index` is certified: in its own deme it is the quadratic
polynomial `X_AB X_ab - X_Ab X_aB`, whose second-order operator is `-D`, in any other deme a
constant. -/
def linkage {D : ℕ} (index : Fin D) : JetPolynomialCertificate (twoLocusLinkageJet index) where
  polynomial deme state := if deme = index then
      MvPolynomial.X .AB * MvPolynomial.X .ab
        + (-1 : ℝ) • (MvPolynomial.X .Ab * MvPolynomial.X .aB)
    else MvPolynomial.C (state index).linkage
  degree := 2
  totalDegree_le deme state := by
    split_ifs
    · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
      · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp [MvPolynomial.totalDegree_X])
      · exact (MvPolynomial.totalDegree_smul_le _ _).trans
          ((MvPolynomial.totalDegree_mul _ _).trans (by simp [MvPolynomial.totalDegree_X]))
    · simp [MvPolynomial.totalDegree_C]
  massBound := 2
  mass_le deme state := by
    split_ifs
    · refine (coefficientMass_add_le _ _).trans ?_
      have hfirst : coefficientMass (MvPolynomial.X TwoLocusHaplotype.AB
          * MvPolynomial.X TwoLocusHaplotype.ab : MvPolynomial TwoLocusHaplotype ℝ) ≤ 1 :=
        (coefficientMass_mul_le _ _).trans (by simp [MvPolynomial.X, coefficientMass_monomial])
      have hsecond : coefficientMass (MvPolynomial.X TwoLocusHaplotype.Ab
          * MvPolynomial.X TwoLocusHaplotype.aB : MvPolynomial TwoLocusHaplotype ℝ) ≤ 1 :=
        (coefficientMass_mul_le _ _).trans (by simp [MvPolynomial.X, coefficientMass_monomial])
      have habs : |(-1 : ℝ)| = 1 := by norm_num
      rw [coefficientMass_smul, habs]
      linarith
    · rw [MvPolynomial.C_apply, coefficientMass_monomial]
      linarith [(state index).linkage_abs_le_quarter]
  polynomial_update deme state frequency := by
    by_cases hdeme : deme = index
    · simp only [if_pos hdeme]
    · simp only [if_neg hdeme, Function.update_of_ne (Ne.symm hdeme)]
  value_eq deme state := by
    by_cases hdeme : deme = index
    · subst hdeme
      rw [if_pos rfl]
      simp only [twoLocusLinkageJet, map_add, map_mul, eval_smul, MvPolynomial.eval_X,
        haplotypeCoordinate, TwoLocusHaplotypeFrequencies.linkage]
      ring
    · rw [if_neg hdeme]
      exact (MvPolynomial.eval_C _).symm
  gradient_eq deme state observed := by
    by_cases hdeme : deme = index
    · subst hdeme
      rw [if_pos rfl]
      cases observed <;>
        simp [twoLocusLinkageJet, twoLocusLinkageGradient, MvPolynomial.pderiv_mul,
          MvPolynomial.pderiv_X, Pi.single_apply, eval_smul, haplotypeCoordinate]
    · rw [if_neg hdeme]
      simp [twoLocusLinkageJet, hdeme, MvPolynomial.pderiv_C]
  drift_eq deme state := by
    by_cases hdeme : deme = index
    · subst hdeme
      rw [if_pos rfl]
      simp only [twoLocusLinkageJet, if_pos rfl, twoLocusLinkageDrift_eq_neg_linkage,
        resamplingOperator_add, resamplingOperator_smul, resamplingOperator_X_mul_X,
        TwoLocusHaplotypeFrequencies.linkage, haplotypeCoordinate, reduceCtorEq, if_false,
        if_true]
      try ring
    · rw [if_neg hdeme]
      simp [twoLocusLinkageJet, hdeme, resamplingOperator, MvPolynomial.pderiv_C]

/-- The centred left-marginal contrast `1 - 2 p` of deme `index`. -/
def leftContrast {D : ℕ} (index : Fin D) :
    JetPolynomialCertificate (twoLocusLeftContrastJet index) :=
  add (const 1) (smul (-2) (leftFrequency index))

/-- The centred right-marginal contrast `1 - 2 q` of deme `index`. -/
def rightContrast {D : ℕ} (index : Fin D) :
    JetPolynomialCertificate (twoLocusRightContrastJet index) :=
  add (const 1) (smul (-2) (rightFrequency index))

/-- The cross-deme left heterozygosity `H_ij`. -/
def heterozygosity {D : ℕ} (first second : Fin D) :
    JetPolynomialCertificate (twoLocusHJet first second) :=
  add (mul (leftFrequency first) (add (const 1) (smul (-1) (leftFrequency second))))
    (mul (leftFrequency second) (add (const 1) (smul (-1) (leftFrequency first))))

/-- The cross-deme right heterozygosity `H^R_ij`. -/
def rightHeterozygosity {D : ℕ} (first second : Fin D) :
    JetPolynomialCertificate (twoLocusRightHJet first second) :=
  add (mul (rightFrequency first) (add (const 1) (smul (-1) (rightFrequency second))))
    (mul (rightFrequency second) (add (const 1) (smul (-1) (rightFrequency first))))

/-- The cross-deme linkage product `DD_ij`. -/
def linkageProduct {D : ℕ} (first second : Fin D) :
    JetPolynomialCertificate (twoLocusDDJet first second) :=
  mul (linkage first) (linkage second)

/-- The generalized `Dz_ijk` observable. -/
def dzObservable {D : ℕ} (first second third : Fin D) :
    JetPolynomialCertificate (twoLocusDzJet first second third) :=
  mul (mul (linkage first) (leftContrast second)) (rightContrast third)

/-- The joint heterozygosity `pi2_ijkl = H_ij H^R_kl / 4`. -/
def jointHeterozygosity {D : ℕ} (first second third fourth : Fin D) :
    JetPolynomialCertificate (twoLocusPi2Jet first second third fourth) :=
  smul (1 / 4) (mul (heterozygosity first second) (rightHeterozygosity third fourth))

/-- The certificate of every stored low-order coordinate jet. -/
def coordinate {D : ℕ} :
    (c : LowOrderLDCoordinate D) → JetPolynomialCertificate (twoLocusCoordinateJet c)
  | .H first second => heterozygosity first second
  | .DD first second => linkageProduct first second
  | .Dz first second third => dzObservable first second third
  | .pi2 first second third fourth => jointHeterozygosity first second third fourth

/-- The certificate of every enlarged coordinate jet of NOTE1 (6). -/
def enlarged {D : ℕ} :
    (c : EnlargedLowOrderLDGenerator.AffineEnlargedCoordinate D) →
      JetPolynomialCertificate (TwoLocusMicroscopicKernel.enlargedCoordinateJet c)
  | none => const 1
  | some (.inl c) => coordinate c
  | some (.inr pair) => rightHeterozygosity pair.1 pair.2

/-- Every enlarged coordinate certificate has total degree at most four. -/
theorem enlarged_degree_le {D : ℕ} (c : EnlargedLowOrderLDGenerator.AffineEnlargedCoordinate D) :
    (enlarged c).degree ≤ 4 := by
  rcases c with _ | ((⟨first, second⟩ | ⟨first, second⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third, fourth⟩) | ⟨first, second⟩) <;>
    exact Nat.le_of_ble_eq_true rfl

end JetPolynomialCertificate

/-! ## The multinomial drift stage on the enlarged coordinates -/

/-- Every enlarged coordinate jet, read in the resampled deme `deme`, is a degree-four observable:
the coefficient bound is read off the certificate's mass, and the drift bound off the corpus
resampling certificate, whose second-order coefficient averages to the drift. -/
def enlargedObservable {D : ℕ} (c : EnlargedLowOrderLDGenerator.AffineEnlargedCoordinate D)
    (deme : Fin D) :
    DegreeFourObservable deme (TwoLocusMicroscopicKernel.enlargedCoordinateJet c).value where
  polynomial := (JetPolynomialCertificate.enlarged c).polynomial deme
  totalDegree_le state := ((JetPolynomialCertificate.enlarged c).totalDegree_le deme state).trans
    (JetPolynomialCertificate.enlarged_degree_le c)
  polynomial_update := (JetPolynomialCertificate.enlarged c).polynomial_update deme
  observable_eq := (JetPolynomialCertificate.enlarged c).value_eq deme
  coefficientBound := 107 * (JetPolynomialCertificate.enlarged c).massBound
  coefficient_le state := (sum_coeff_remainder_le _
      (((JetPolynomialCertificate.enlarged c).totalDegree_le deme state).trans
        (JetPolynomialCertificate.enlarged_degree_le c))).trans
    (mul_le_mul_of_nonneg_left ((JetPolynomialCertificate.enlarged c).mass_le deme state)
      (by norm_num))
  driftBound := (TwoLocusMicroscopicKernel.enlargedStageExpansion c).drift.bound
  drift_le state := by
    rw [← (JetPolynomialCertificate.enlarged c).drift_eq deme state,
      ← (TwoLocusMicroscopicKernel.enlargedStageExpansion c).drift.second_mean deme state]
    exact twoLocusHaplotypeMean_abs_le _ _ _
      ((TwoLocusMicroscopicKernel.enlargedStageExpansion c).drift.second_le deme state)

/-- **One multinomial drift stage moves every enlarged coordinate by its corpus drift.** At rate
`rate > 0` and step size `step > 0` the multinomial drift stage in deme `deme` moves the enlarged
coordinate jet by `step · rate · driftAt`, up to `step · rate ^ 2 · step` times an explicit
constant. -/
theorem apply_multinomialDriftStage_enlarged {D : ℕ}
    (c : EnlargedLowOrderLDGenerator.AffineEnlargedCoordinate D) (deme : Fin D)
    (rate step : ℝ) (hrate : 0 < rate) (hstep : 0 < step)
    (state : Fin D → TwoLocusHaplotypeFrequencies) :
    |(multinomialDriftKernel deme (one_le_multinomialChromosomeCount rate step hrate hstep)).apply
          (TwoLocusMicroscopicKernel.enlargedCoordinateJet c).value state
        - (TwoLocusMicroscopicKernel.enlargedCoordinateJet c).value state
        - step * (rate * (TwoLocusMicroscopicKernel.enlargedCoordinateJet c).driftAt deme state)|
      ≤ step * (rate ^ 2 * step * (107 * (JetPolynomialCertificate.enlarged c).massBound
          + (TwoLocusMicroscopicKernel.enlargedStageExpansion c).drift.bound)) := by
  rw [(JetPolynomialCertificate.enlarged c).drift_eq deme state]
  exact apply_multinomialDriftStage_expansion (enlargedObservable c deme) rate step hrate hstep
    state

end

end Descent.Portability.MultinomialJetCertificate
