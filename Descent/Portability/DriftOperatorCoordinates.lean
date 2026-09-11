/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EnlargedLowOrderLDGenerator
import Mathlib.Algebra.MvPolynomial.PDeriv

assert_below Descent.Decision Descent.Program

/-!
# The drift operator of NOTE1 equation (7) in the coordinates `p`, `q`, `D`

NOTE1 equation (7) writes the neutral drift generator of one deme as a second-order differential
operator in the deme's left allele frequency `p`, right allele frequency `q` and linkage
determinant `D`:

`L f = -D ∂_D f + ½ p(1-p) ∂_pp f + ½ q(1-q) ∂_qq f + D ∂_pq f + D(1-2p) ∂_Dp f`
`      + D(1-2q) ∂_Dq f + ½ [p(1-p) q(1-q) + D(1-2p)(1-2q) - D²] ∂_DD f`,

and illustrates it by `L D² = -3 D² + Dz + π` and `L Dz = 4 D² - 5 Dz`.  The corpus never writes
this operator: its drift rows are built from diffusion jets whose drift of a product is fixed by
the multinomial-covariance product rule.  This module states the operator literally,
`driftOperator` on `MvPolynomial (Fin 3) ℝ` with the variables `p`, `q`, `D` and Mathlib's
partial derivatives, proves the two displayed identities (`driftOperator_linkage_sq`,
`driftOperator_dzObservable`), and proves that it is the operator the corpus drift rows encode.

The bridge is a product rule on both sides.  `driftOperator_mul` is the Leibniz rule of the
operator with its field operator `fieldOperator`, and `covariance_chainRule` shows that the
multinomial covariance of two chain-rule gradients through `p`, `q`, `D` is that field operator
at the deme's frequencies.  `JetRepresentation deme jet polynomial` says a corpus jet has, at
`deme`, the value, the drift and the chain-rule gradient of a state-dependent polynomial in that
deme's coordinates; it holds for constants and the three base coordinates (`leftSlot`,
`rightSlot`, `linkageSlot`, the variable when the index is the drifting deme and a constant
otherwise) and is closed under sums, scalar multiples and products.  Every stored coordinate jet
is assembled from those, so `JetRepresentation.coordinate` holds with `featurePolynomial`, and
`lowOrderLDDrift_eq_driftOperator` says the drift row of `enlargedLowOrderLDGenerator` on every
stored coordinate is the operator (7) applied to the feature polynomial at each deme and summed
against the coalescence rates.  The right-locus heterozygosity that the enlarged family adds is
represented the same way (`JetRepresentation.rightHeterozygosity`).

Scope.  The operator is stated on polynomials, which is all the feature family needs; no analytic
generator on smooth functions of the simplex is constructed.

## Empirical status

None.  The bodies here are algebra: partial derivatives of polynomials and multinomial covariances
of polynomial scores, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.DriftOperatorCoordinates

open Coalescent
open MvPolynomial

noncomputable section

/-! ## The operator of equation (7) -/

/-- Polynomials in the three within-deme coordinates of NOTE1 equation (7): variable `0` is the
left allele frequency `p`, `1` the right allele frequency `q`, and `2` the linkage determinant
`D`. -/
abbrev CoordinatePolynomial := MvPolynomial (Fin 3) ℝ

/-- **The drift operator of NOTE1 equation (7)** on polynomials in `p`, `q`, `D`. -/
def driftOperator (f : CoordinatePolynomial) : CoordinatePolynomial :=
  -(X 2 * pderiv 2 f) +
    C (1 / 2) * (X 0 * (1 - X 0)) * pderiv 0 (pderiv 0 f) +
    C (1 / 2) * (X 1 * (1 - X 1)) * pderiv 1 (pderiv 1 f) +
    X 2 * pderiv 0 (pderiv 1 f) +
    X 2 * (1 - 2 * X 0) * pderiv 2 (pderiv 0 f) +
    X 2 * (1 - 2 * X 1) * pderiv 2 (pderiv 1 f) +
    C (1 / 2) * (X 0 * (1 - X 0) * (X 1 * (1 - X 1)) + X 2 * (1 - 2 * X 0) * (1 - 2 * X 1) -
      X 2 ^ 2) * pderiv 2 (pderiv 2 f)

/-- The field operator of `driftOperator`: the bilinear part a product picks up, from the
second-order coefficients of equation (7). -/
def fieldOperator (f g : CoordinatePolynomial) : CoordinatePolynomial :=
  C (1 / 2) * (X 0 * (1 - X 0)) * (pderiv 0 f * pderiv 0 g + pderiv 0 g * pderiv 0 f) +
    C (1 / 2) * (X 1 * (1 - X 1)) * (pderiv 1 f * pderiv 1 g + pderiv 1 g * pderiv 1 f) +
    X 2 * (pderiv 0 f * pderiv 1 g + pderiv 1 f * pderiv 0 g) +
    X 2 * (1 - 2 * X 0) * (pderiv 2 f * pderiv 0 g + pderiv 0 f * pderiv 2 g) +
    X 2 * (1 - 2 * X 1) * (pderiv 2 f * pderiv 1 g + pderiv 1 f * pderiv 2 g) +
    C (1 / 2) * (X 0 * (1 - X 0) * (X 1 * (1 - X 1)) + X 2 * (1 - 2 * X 0) * (1 - 2 * X 1) -
      X 2 ^ 2) * (pderiv 2 f * pderiv 2 g + pderiv 2 g * pderiv 2 f)

private theorem pderiv_zero_X_zero : pderiv 0 (X 0 : CoordinatePolynomial) = 1 :=
  pderiv_X_self 0

private theorem pderiv_one_X_zero : pderiv 1 (X 0 : CoordinatePolynomial) = 0 :=
  pderiv_X_of_ne (by decide)

private theorem pderiv_two_X_zero : pderiv 2 (X 0 : CoordinatePolynomial) = 0 :=
  pderiv_X_of_ne (by decide)

private theorem pderiv_zero_X_one : pderiv 0 (X 1 : CoordinatePolynomial) = 0 :=
  pderiv_X_of_ne (by decide)

private theorem pderiv_one_X_one : pderiv 1 (X 1 : CoordinatePolynomial) = 1 :=
  pderiv_X_self 1

private theorem pderiv_two_X_one : pderiv 2 (X 1 : CoordinatePolynomial) = 0 :=
  pderiv_X_of_ne (by decide)

private theorem pderiv_zero_X_two : pderiv 0 (X 2 : CoordinatePolynomial) = 0 :=
  pderiv_X_of_ne (by decide)

private theorem pderiv_one_X_two : pderiv 1 (X 2 : CoordinatePolynomial) = 0 :=
  pderiv_X_of_ne (by decide)

private theorem pderiv_two_X_two : pderiv 2 (X 2 : CoordinatePolynomial) = 1 :=
  pderiv_X_self 2

private theorem pderiv_ofNat_two (i : Fin 3) : pderiv i (2 : CoordinatePolynomial) = 0 := by
  rw [← map_ofNat C 2]
  exact pderiv_C

/-- The operator is additive. -/
theorem driftOperator_add (f g : CoordinatePolynomial) :
    driftOperator (f + g) = driftOperator f + driftOperator g := by
  simp only [driftOperator, map_add]
  ring

/-- The operator commutes with constant multiples. -/
theorem driftOperator_C_mul (level : ℝ) (f : CoordinatePolynomial) :
    driftOperator (C level * f) = C level * driftOperator f := by
  simp only [driftOperator, pderiv_C_mul]
  ring

/-- The operator annihilates constants. -/
theorem driftOperator_C (level : ℝ) : driftOperator (C level) = 0 := by
  simp only [driftOperator, pderiv_C, map_zero]
  ring

/-- **The Leibniz rule of equation (7).**  The drift of a product is each factor times the drift
of the other plus the field operator of the two factors. -/
theorem driftOperator_mul (f g : CoordinatePolynomial) :
    driftOperator (f * g) = f * driftOperator g + g * driftOperator f + fieldOperator f g := by
  simp only [driftOperator, fieldOperator, Derivation.leibniz, smul_eq_mul, map_add]
  ring

/-- The left allele frequency does not drift. -/
theorem driftOperator_X_zero : driftOperator (X 0) = 0 := by
  simp only [driftOperator, pderiv_zero_X_zero, pderiv_one_X_zero, pderiv_two_X_zero,
    Derivation.map_one_eq_zero, map_zero]
  ring

/-- The right allele frequency does not drift. -/
theorem driftOperator_X_one : driftOperator (X 1) = 0 := by
  simp only [driftOperator, pderiv_zero_X_one, pderiv_one_X_one, pderiv_two_X_one,
    Derivation.map_one_eq_zero, map_zero]
  ring

/-- The linkage determinant decays at unit rate. -/
theorem driftOperator_X_two : driftOperator (X 2) = -X 2 := by
  simp only [driftOperator, pderiv_zero_X_two, pderiv_one_X_two, pderiv_two_X_two,
    Derivation.map_one_eq_zero, map_zero]
  ring

/-- **NOTE1's first example: `L D² = -3 D² + Dz + π`**, with `Dz = D (1-2p)(1-2q)` and
`π = p(1-p) q(1-q)` the within-deme `Dz` and `pi2`. -/
theorem driftOperator_linkage_sq :
    driftOperator (X 2 ^ 2) =
      -3 * X 2 ^ 2 + X 2 * (1 - 2 * X 0) * (1 - 2 * X 1) +
        X 0 * (1 - X 0) * (X 1 * (1 - X 1)) := by
  have hhalf : (C (1 / 2) : CoordinatePolynomial) * 2 = 1 := by
    rw [← map_ofNat C 2, ← map_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, map_one]
  simp only [driftOperator, sq, Derivation.leibniz, smul_eq_mul, map_add, pderiv_zero_X_two,
    pderiv_one_X_two, pderiv_two_X_two, Derivation.map_one_eq_zero, map_zero]
  linear_combination
    (X 0 * (1 - X 0) * (X 1 * (1 - X 1)) + X 2 * (1 - 2 * X 0) * (1 - 2 * X 1) - X 2 ^ 2) * hhalf

/-- **NOTE1's second example: `L Dz = 4 D² - 5 Dz`**, with `Dz = D (1-2p)(1-2q)`. -/
theorem driftOperator_dzObservable :
    driftOperator (X 2 * (1 - 2 * X 0) * (1 - 2 * X 1)) =
      4 * X 2 ^ 2 - 5 * (X 2 * (1 - 2 * X 0) * (1 - 2 * X 1)) := by
  simp only [driftOperator, Derivation.leibniz, smul_eq_mul, map_add, map_sub,
    pderiv_zero_X_zero, pderiv_one_X_zero, pderiv_two_X_zero, pderiv_zero_X_one,
    pderiv_one_X_one, pderiv_two_X_one, pderiv_zero_X_two, pderiv_one_X_two, pderiv_two_X_two,
    pderiv_ofNat_two, Derivation.map_one_eq_zero, map_zero]
  ring

/-! ## The multinomial covariance is the field operator -/

/-- The within-deme coordinates `p`, `q`, `D` of one deme's haplotype frequencies. -/
def coordinates (frequency : TwoLocusHaplotypeFrequencies) : Fin 3 → ℝ
  | 0 => frequency.leftFrequency
  | 1 => frequency.rightFrequency
  | 2 => frequency.linkage

/-- **The covariance of chain-rule gradients is the field operator of (7).**  The multinomial
covariance of two haplotype scores that are combinations of the gradients of `p`, `q` and `D`
is the second-order coefficient matrix of equation (7) paired with the two coefficient
vectors. -/
theorem covariance_chainRule (frequency : TwoLocusHaplotypeFrequencies)
    (leftFirst rightFirst linkageFirst leftSecond rightSecond linkageSecond : ℝ) :
    twoLocusHaplotypeCovariance frequency
        (fun haplotype ↦ leftFirst * twoLocusLeftAlleleIndicator haplotype +
          rightFirst * twoLocusRightAlleleIndicator haplotype +
          linkageFirst * twoLocusLinkageGradient frequency haplotype)
        (fun haplotype ↦ leftSecond * twoLocusLeftAlleleIndicator haplotype +
          rightSecond * twoLocusRightAlleleIndicator haplotype +
          linkageSecond * twoLocusLinkageGradient frequency haplotype) =
      frequency.leftFrequency * (1 - frequency.leftFrequency) * (leftFirst * leftSecond) +
        frequency.rightFrequency * (1 - frequency.rightFrequency) *
          (rightFirst * rightSecond) +
        frequency.linkage * (leftFirst * rightSecond + rightFirst * leftSecond) +
        frequency.linkage * (1 - 2 * frequency.leftFrequency) *
          (linkageFirst * leftSecond + leftFirst * linkageSecond) +
        frequency.linkage * (1 - 2 * frequency.rightFrequency) *
          (linkageFirst * rightSecond + rightFirst * linkageSecond) +
        (frequency.leftFrequency * (1 - frequency.leftFrequency) *
            (frequency.rightFrequency * (1 - frequency.rightFrequency)) +
          frequency.linkage * (1 - 2 * frequency.leftFrequency) *
            (1 - 2 * frequency.rightFrequency) - frequency.linkage ^ 2) *
          (linkageFirst * linkageSecond) := by
  have hab : frequency.ab = 1 - frequency.AB - frequency.Ab - frequency.aB := by
    linarith [frequency.total_eq_one]
  simp only [twoLocusHaplotypeCovariance, twoLocusHaplotypeMean, twoLocusLeftAlleleIndicator,
    twoLocusRightAlleleIndicator, twoLocusLinkageGradient, TwoLocusHaplotypeFrequencies.linkage,
    TwoLocusHaplotypeFrequencies.leftFrequency, TwoLocusHaplotypeFrequencies.rightFrequency, hab]
  ring

/-! ## Corpus jets represent polynomials in the drifting deme's coordinates -/

/-- A corpus diffusion jet represents, at `deme`, a state-dependent polynomial in that deme's
coordinates `p`, `q`, `D` when its value, its drift at `deme` and its gradient at `deme` are the
polynomial's value, the operator (7) applied to the polynomial, and the chain rule through the
three coordinates. -/
structure JetRepresentation {D : ℕ} (deme : Fin D) (jet : TwoLocusDiffusionJet D)
    (polynomial : (Fin D → TwoLocusHaplotypeFrequencies) → CoordinatePolynomial) : Prop where
  value_eq : ∀ state, jet.value state = eval (coordinates (state deme)) (polynomial state)
  drift_eq : ∀ state,
    jet.driftAt deme state = eval (coordinates (state deme)) (driftOperator (polynomial state))
  gradient_eq : ∀ state, jet.gradientAt deme state = fun haplotype ↦
    eval (coordinates (state deme)) (pderiv 0 (polynomial state)) *
        twoLocusLeftAlleleIndicator haplotype +
      eval (coordinates (state deme)) (pderiv 1 (polynomial state)) *
        twoLocusRightAlleleIndicator haplotype +
      eval (coordinates (state deme)) (pderiv 2 (polynomial state)) *
        twoLocusLinkageGradient (state deme) haplotype

/-- A constant jet represents the constant polynomial at every deme. -/
theorem JetRepresentation.const {D : ℕ} (deme : Fin D) (level : ℝ) :
    JetRepresentation deme (TwoLocusDiffusionJet.const level) (fun _ ↦ C level) where
  value_eq _ := (eval_C level).symm
  drift_eq _ := by
    rw [driftOperator_C, map_zero]
    rfl
  gradient_eq _ := by
    funext haplotype
    simp only [pderiv_C, map_zero, zero_mul, add_zero]
    rfl

/-- Representations add. -/
theorem JetRepresentation.add {D : ℕ} {deme : Fin D} {first second : TwoLocusDiffusionJet D}
    {firstPolynomial secondPolynomial :
      (Fin D → TwoLocusHaplotypeFrequencies) → CoordinatePolynomial}
    (hfirst : JetRepresentation deme first firstPolynomial)
    (hsecond : JetRepresentation deme second secondPolynomial) :
    JetRepresentation deme (first.add second)
      (fun state ↦ firstPolynomial state + secondPolynomial state) where
  value_eq state := by
    show first.value state + second.value state = _
    rw [hfirst.value_eq, hsecond.value_eq, map_add]
  drift_eq state := by
    show first.driftAt deme state + second.driftAt deme state = _
    rw [hfirst.drift_eq, hsecond.drift_eq, driftOperator_add, map_add]
  gradient_eq state := by
    funext haplotype
    show first.gradientAt deme state haplotype + second.gradientAt deme state haplotype = _
    rw [hfirst.gradient_eq, hsecond.gradient_eq]
    simp only [map_add]
    ring

/-- Representations are closed under real multiples. -/
theorem JetRepresentation.smul {D : ℕ} {deme : Fin D} {jet : TwoLocusDiffusionJet D}
    {polynomial : (Fin D → TwoLocusHaplotypeFrequencies) → CoordinatePolynomial} (scalar : ℝ)
    (hjet : JetRepresentation deme jet polynomial) :
    JetRepresentation deme (TwoLocusDiffusionJet.smul scalar jet)
      (fun state ↦ C scalar * polynomial state) where
  value_eq state := by
    show scalar * jet.value state = _
    rw [hjet.value_eq, map_mul, eval_C]
  drift_eq state := by
    show scalar * jet.driftAt deme state = _
    rw [hjet.drift_eq, driftOperator_C_mul, map_mul, eval_C]
  gradient_eq state := by
    funext haplotype
    show scalar * jet.gradientAt deme state haplotype = _
    rw [hjet.gradient_eq]
    simp only [pderiv_C_mul, map_mul, eval_C]
    ring

/-- **Representations multiply.**  The corpus product rule adds the multinomial covariance of the
two gradients, and by `covariance_chainRule` that is the field operator of the two polynomials,
which is exactly what `driftOperator_mul` adds. -/
theorem JetRepresentation.mul {D : ℕ} {deme : Fin D} {first second : TwoLocusDiffusionJet D}
    {firstPolynomial secondPolynomial :
      (Fin D → TwoLocusHaplotypeFrequencies) → CoordinatePolynomial}
    (hfirst : JetRepresentation deme first firstPolynomial)
    (hsecond : JetRepresentation deme second secondPolynomial) :
    JetRepresentation deme (first.mul second)
      (fun state ↦ firstPolynomial state * secondPolynomial state) where
  value_eq state := by
    show first.value state * second.value state = _
    rw [hfirst.value_eq, hsecond.value_eq, map_mul]
  drift_eq state := by
    show first.value state * second.driftAt deme state +
        second.value state * first.driftAt deme state +
        twoLocusHaplotypeCovariance (state deme) (first.gradientAt deme state)
          (second.gradientAt deme state) = _
    rw [hfirst.value_eq, hsecond.value_eq, hfirst.drift_eq, hsecond.drift_eq,
      hfirst.gradient_eq, hsecond.gradient_eq, covariance_chainRule, driftOperator_mul]
    simp only [fieldOperator, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, eval_C,
      eval_X, coordinates]
    ring
  gradient_eq state := by
    funext haplotype
    show first.value state * second.gradientAt deme state haplotype +
        second.value state * first.gradientAt deme state haplotype = _
    rw [hfirst.value_eq, hsecond.value_eq, hfirst.gradient_eq, hsecond.gradient_eq]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul]
    ring

/-- The left allele frequency of deme `index`, read at `deme`: the variable `p` when the two demes
coincide and a constant otherwise. -/
def leftSlot {D : ℕ} (deme index : Fin D) (state : Fin D → TwoLocusHaplotypeFrequencies) :
    CoordinatePolynomial :=
  if deme = index then X 0 else C (state index).leftFrequency

/-- The right allele frequency of deme `index`, read at `deme`. -/
def rightSlot {D : ℕ} (deme index : Fin D) (state : Fin D → TwoLocusHaplotypeFrequencies) :
    CoordinatePolynomial :=
  if deme = index then X 1 else C (state index).rightFrequency

/-- The linkage determinant of deme `index`, read at `deme`. -/
def linkageSlot {D : ℕ} (deme index : Fin D) (state : Fin D → TwoLocusHaplotypeFrequencies) :
    CoordinatePolynomial :=
  if deme = index then X 2 else C (state index).linkage

/-- The corpus left-frequency jet represents its slot. -/
theorem JetRepresentation.leftFrequency {D : ℕ} (deme index : Fin D) :
    JetRepresentation deme (twoLocusLeftFrequencyJet index) (leftSlot deme index) where
  value_eq state := by
    by_cases hdeme : deme = index
    · subst hdeme
      rw [leftSlot, if_pos rfl, eval_X]
      rfl
    · rw [leftSlot, if_neg hdeme, eval_C]
      rfl
  drift_eq state := by
    by_cases hdeme : deme = index
    · rw [leftSlot, if_pos hdeme, driftOperator_X_zero, map_zero]
      rfl
    · rw [leftSlot, if_neg hdeme, driftOperator_C, map_zero]
      rfl
  gradient_eq state := by
    funext haplotype
    show (if deme = index then twoLocusLeftAlleleIndicator haplotype else 0) = _
    by_cases hdeme : deme = index
    · rw [if_pos hdeme, leftSlot, if_pos hdeme, pderiv_zero_X_zero, pderiv_one_X_zero,
        pderiv_two_X_zero, map_one, map_zero]
      ring
    · rw [if_neg hdeme, leftSlot, if_neg hdeme, pderiv_C, pderiv_C, pderiv_C, map_zero]
      ring

/-- The corpus right-frequency jet represents its slot. -/
theorem JetRepresentation.rightFrequency {D : ℕ} (deme index : Fin D) :
    JetRepresentation deme (twoLocusRightFrequencyJet index) (rightSlot deme index) where
  value_eq state := by
    by_cases hdeme : deme = index
    · subst hdeme
      rw [rightSlot, if_pos rfl, eval_X]
      rfl
    · rw [rightSlot, if_neg hdeme, eval_C]
      rfl
  drift_eq state := by
    by_cases hdeme : deme = index
    · rw [rightSlot, if_pos hdeme, driftOperator_X_one, map_zero]
      rfl
    · rw [rightSlot, if_neg hdeme, driftOperator_C, map_zero]
      rfl
  gradient_eq state := by
    funext haplotype
    show (if deme = index then twoLocusRightAlleleIndicator haplotype else 0) = _
    by_cases hdeme : deme = index
    · rw [if_pos hdeme, rightSlot, if_pos hdeme, pderiv_zero_X_one, pderiv_one_X_one,
        pderiv_two_X_one, map_one, map_zero]
      ring
    · rw [if_neg hdeme, rightSlot, if_neg hdeme, pderiv_C, pderiv_C, pderiv_C, map_zero]
      ring

/-- The corpus linkage jet represents its slot: at the drifting deme its drift is the corpus
`-D`, which is `driftOperator_X_two`. -/
theorem JetRepresentation.linkage {D : ℕ} (deme index : Fin D) :
    JetRepresentation deme (twoLocusLinkageJet index) (linkageSlot deme index) where
  value_eq state := by
    by_cases hdeme : deme = index
    · subst hdeme
      rw [linkageSlot, if_pos rfl, eval_X]
      rfl
    · rw [linkageSlot, if_neg hdeme, eval_C]
      rfl
  drift_eq state := by
    show (if deme = index then twoLocusLinkageDrift (state index) else 0) = _
    by_cases hdeme : deme = index
    · subst hdeme
      rw [if_pos rfl, twoLocusLinkageDrift_eq_neg_linkage, linkageSlot, if_pos rfl,
        driftOperator_X_two, map_neg, eval_X]
      rfl
    · rw [if_neg hdeme, linkageSlot, if_neg hdeme, driftOperator_C, map_zero]
  gradient_eq state := by
    funext haplotype
    show (if deme = index then twoLocusLinkageGradient (state index) haplotype else 0) = _
    by_cases hdeme : deme = index
    · subst hdeme
      rw [if_pos rfl, linkageSlot, if_pos rfl, pderiv_zero_X_two, pderiv_one_X_two,
        pderiv_two_X_two, map_one, map_zero]
      ring
    · rw [if_neg hdeme, linkageSlot, if_neg hdeme, pderiv_C, pderiv_C, pderiv_C, map_zero]
      ring

/-! ## The feature family -/

/-- The polynomial of the cross-deme left heterozygosity at `deme`, in the shape of the corpus
jet `twoLocusHJet`. -/
def heterozygosityPolynomial {D : ℕ} (deme first second : Fin D)
    (state : Fin D → TwoLocusHaplotypeFrequencies) : CoordinatePolynomial :=
  leftSlot deme first state * (C 1 + C (-1) * leftSlot deme second state) +
    leftSlot deme second state * (C 1 + C (-1) * leftSlot deme first state)

/-- The polynomial of the cross-deme right heterozygosity at `deme`, in the shape of the corpus
jet `twoLocusRightHJet`. -/
def rightHeterozygosityPolynomial {D : ℕ} (deme first second : Fin D)
    (state : Fin D → TwoLocusHaplotypeFrequencies) : CoordinatePolynomial :=
  rightSlot deme first state * (C 1 + C (-1) * rightSlot deme second state) +
    rightSlot deme second state * (C 1 + C (-1) * rightSlot deme first state)

/-- The polynomial of every stored coordinate at `deme`, in the shape of the corpus jets:
`H`, the linkage product `DD`, the generalized `Dz`, and the joint heterozygosity `pi2`. -/
def featurePolynomial {D : ℕ} (deme : Fin D) :
    LowOrderLDCoordinate D → (Fin D → TwoLocusHaplotypeFrequencies) → CoordinatePolynomial
  | .H first second => heterozygosityPolynomial deme first second
  | .DD first second => fun state ↦ linkageSlot deme first state * linkageSlot deme second state
  | .Dz first second third => fun state ↦
      linkageSlot deme first state * (C 1 + C (-2) * leftSlot deme second state) *
        (C 1 + C (-2) * rightSlot deme third state)
  | .pi2 first second third fourth => fun state ↦
      C (1 / 4) * (heterozygosityPolynomial deme first second state *
        rightHeterozygosityPolynomial deme third fourth state)

/-- The corpus left-heterozygosity jet represents its polynomial. -/
theorem JetRepresentation.heterozygosity {D : ℕ} (deme first second : Fin D) :
    JetRepresentation deme (twoLocusHJet first second)
      (heterozygosityPolynomial deme first second) :=
  ((JetRepresentation.leftFrequency deme first).mul
      ((JetRepresentation.const deme 1).add
        ((JetRepresentation.leftFrequency deme second).smul (-1)))).add
    ((JetRepresentation.leftFrequency deme second).mul
      ((JetRepresentation.const deme 1).add
        ((JetRepresentation.leftFrequency deme first).smul (-1))))

/-- **The right-locus heterozygosity that the enlarged family adds is represented too.** -/
theorem JetRepresentation.rightHeterozygosity {D : ℕ} (deme first second : Fin D) :
    JetRepresentation deme (twoLocusRightHJet first second)
      (rightHeterozygosityPolynomial deme first second) :=
  ((JetRepresentation.rightFrequency deme first).mul
      ((JetRepresentation.const deme 1).add
        ((JetRepresentation.rightFrequency deme second).smul (-1)))).add
    ((JetRepresentation.rightFrequency deme second).mul
      ((JetRepresentation.const deme 1).add
        ((JetRepresentation.rightFrequency deme first).smul (-1))))

/-- **Every stored coordinate jet represents its feature polynomial.** -/
theorem JetRepresentation.coordinate {D : ℕ} (deme : Fin D) :
    ∀ coordinate : LowOrderLDCoordinate D,
      JetRepresentation deme (twoLocusCoordinateJet coordinate) (featurePolynomial deme coordinate)
  | .H first second => JetRepresentation.heterozygosity deme first second
  | .DD first second =>
      (JetRepresentation.linkage deme first).mul (JetRepresentation.linkage deme second)
  | .Dz first second third =>
      ((JetRepresentation.linkage deme first).mul
          ((JetRepresentation.const deme 1).add
            ((JetRepresentation.leftFrequency deme second).smul (-2)))).mul
        ((JetRepresentation.const deme 1).add
          ((JetRepresentation.rightFrequency deme third).smul (-2)))
  | .pi2 first second third fourth =>
      ((JetRepresentation.heterozygosity deme first second).mul
        (JetRepresentation.rightHeterozygosity deme third fourth)).smul (1 / 4)

/-! ## Agreement with the corpus drift rows -/

/-- **The corpus drift of every stored coordinate at a deme is the operator (7).** -/
theorem coordinateJet_driftAt_eq_driftOperator {D : ℕ} (deme : Fin D)
    (coordinate : LowOrderLDCoordinate D) (state : Fin D → TwoLocusHaplotypeFrequencies) :
    (twoLocusCoordinateJet coordinate).driftAt deme state =
      eval (coordinates (state deme)) (driftOperator (featurePolynomial deme coordinate state)) :=
  (JetRepresentation.coordinate deme coordinate).drift_eq state

/-- The corpus drift of the right-locus heterozygosity at a deme is the operator (7). -/
theorem rightHeterozygosityJet_driftAt_eq_driftOperator {D : ℕ} (deme first second : Fin D)
    (state : Fin D → TwoLocusHaplotypeFrequencies) :
    (twoLocusRightHJet first second).driftAt deme state =
      eval (coordinates (state deme))
        (driftOperator (rightHeterozygosityPolynomial deme first second state)) :=
  (JetRepresentation.rightHeterozygosity deme first second).drift_eq state

/-- **The drift rows of the enlarged generator are the operator of equation (7).**  On every
stored coordinate, the drift row of `enlargedLowOrderLDGenerator`, the corpus `lowOrderLDDrift`
read at the moment vector of a haplotype configuration, is the operator (7) applied at each deme
to the coordinate's feature polynomial and summed against the coalescence rates. -/
theorem lowOrderLDDrift_eq_driftOperator {D : ℕ} (rates : ManyDemeLDRates D)
    (state : Fin D → TwoLocusHaplotypeFrequencies) (coordinate : LowOrderLDCoordinate D) :
    lowOrderLDDrift rates (twoLocusJetMoment state) coordinate =
      ∑ deme, rates.coalescence deme *
        eval (coordinates (state deme)) (driftOperator (featurePolynomial deme coordinate state)) := by
  have hweighted : lowOrderLDDrift rates (twoLocusJetMoment state) coordinate =
      twoLocusWeightedJetDrift rates.coalescence state coordinate := by
    cases coordinate with
    | H first second =>
        exact (twoLocusWeightedJetDrift_H_eq_lowOrderLDDrift rates state first second).symm
    | DD first second =>
        exact (twoLocusWeightedJetDrift_DD_eq_lowOrderLDDrift rates state first second).symm
    | Dz first second third =>
        exact (twoLocusWeightedJetDrift_Dz_eq_lowOrderLDDrift rates state first second
          third).symm
    | pi2 first second third fourth =>
        exact (twoLocusWeightedJetDrift_pi2_eq_lowOrderLDDrift rates state first second third
          fourth).symm
  rw [hweighted, twoLocusWeightedJetDrift]
  exact Finset.sum_congr rfl fun deme _ ↦ by
    rw [coordinateJet_driftAt_eq_driftOperator]

/-- The enlarged generator's stored rows at haplotype-configuration moments carry this drift: at
rates with no migration, mutation or recombination the whole stored row is the operator (7)
summed against the coalescence rates, plus the vanishing mutation forcing. -/
theorem enlargedGenerator_stored_driftRow {D : ℕ} (rates : ManyDemeLDRates D)
    (state : Fin D → TwoLocusHaplotypeFrequencies) (coordinate : LowOrderLDCoordinate D) :
    lowOrderLDHomogeneousGenerator rates (twoLocusJetMoment state) coordinate =
      (∑ deme, rates.coalescence deme *
          eval (coordinates (state deme))
            (driftOperator (featurePolynomial deme coordinate state))) +
        lowOrderLDMigration rates (twoLocusJetMoment state) coordinate +
        lowOrderLDRecombination rates (twoLocusJetMoment state) coordinate +
        lowOrderLDMutationCoupling rates (twoLocusJetMoment state) coordinate +
        lowOrderLDRecurrentMutationDamping rates (twoLocusJetMoment state) coordinate := by
  rw [lowOrderLDHomogeneousGenerator, lowOrderLDDrift_eq_driftOperator]

end

end Descent.Portability.DriftOperatorCoordinates
