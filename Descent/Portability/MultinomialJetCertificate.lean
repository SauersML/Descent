/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MultinomialDriftStage

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
and scalar multiples, adding degrees by maximum and masses by sum.

What is NOT proved in this module yet: the product closure, which needs the product rule of the
second-order operator against the corpus's multinomial covariance; the base certificates for the
marginal frequency and linkage jets; and the certificates of the enlarged coordinate jets.

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

end JetPolynomialCertificate

end

end Descent.Portability.MultinomialJetCertificate
