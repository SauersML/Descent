/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.TwoLocusHistory

assert_below Descent.Decision Descent.Program

/-!
# Second-order expansions of the deterministic two-locus pulse stages

NOTE1 section 2.3 builds a positive microscopic kernel out of stages, three of which are
deterministic: a haplotype-level migration pulse of fraction `h m_ij`, a recombination pulse
of fraction `h rho_i / 2` toward the product of the two marginal allele laws, and symmetric
allele-flip mutation pulses of probability `h theta_i / 2` at each locus.  Theorem 1 of NOTE1
needs every stage to satisfy the uniform expansion of its equation (3),
`K_h phi = phi + h A phi + O(h^2)`.  This module supplies the deterministic half of that
requirement, in the exact pointwise form the corpus's own pulse laws already carry.

`PulseExpansion pulse observable` is the expansion certificate: a first-order `velocity`, a
uniform quadratic `remainder`, and uniform sup-norm bounds on the observable and on its
velocity.  It is closed under constants, sums, scalar multiples, and products; the product
rule carries the Leibniz velocity `f v_g + g v_f` together with a remainder assembled from the
factor bounds.  Every member of the closed low-order family is reached from the three base
coordinates of a deme -- the two marginal allele frequencies and the linkage determinant -- by
those four operations, so one `PulseCoordinateExpansion` yields an expansion of
`twoLocusCoordinateJet c` for every `c : LowOrderLDCoordinate D` and of `twoLocusRightHJet`,
the right-locus heterozygosity that NOTE1 equation (6) adds to the stored family.

The three pulse families are defined with their fractions clamped into `[0,1]`, so each is a
total map of the deme state space for every real parameter; the expansion statements assume
`0 ≤ tau ≤ 1`, where the clamp is inactive.  Migration is the only stage with a nonzero
remainder: `mixture_linkage_eq_velocity` makes its linkage law exactly quadratic, with cross
term `(p_source - p_recipient)(q_source - q_recipient)`, bounded by one on the simplex.
Recombination and both mutation pulses are exactly affine in their fraction on all three base
coordinates, so their remainders are zero rather than merely small.

What is NOT proved here is the identification of every composite velocity with the matching
row of `lowOrderLDHomogeneousGenerator`.  Four such bridges are proved, in the pointwise
per-pulse form used by the corpus family `lowOrderLDMigration_H_eq_haplotypeVelocity`: the
left- and right-heterozygosity migration rows, the `DD` recombination row, and the
left-heterozygosity mutation row.  The remaining coordinate-by-pulse identities, and the whole
random resampling stage, belong to other modules.

## Empirical status

None.  The bodies here are algebra: every statement is an identity or an inequality between
polynomials in haplotype frequencies on the probability simplex, so no measurement can bear
on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PulseJetExpansion

open Coalescent
open Coalescent.TwoLocusHaplotypeFrequencies

noncomputable section

/-- Haplotype-frequency configuration of every deme, the state space `X = (Delta_3)^d` of
NOTE1 section 2.2. -/
abbrev DemeHaplotypeState (D : ℕ) := Fin D → TwoLocusHaplotypeFrequencies

/-! ## Clamped pulse fractions -/

/-- Pulse parameter clamped into the unit interval, so that every stage is a total map of the
deme state space for an arbitrary real parameter. -/
def pulseFraction (tau : ℝ) : ℝ := min 1 (max 0 tau)

theorem pulseFraction_nonneg (tau : ℝ) : 0 ≤ pulseFraction tau :=
  le_min zero_le_one (le_max_left 0 tau)

theorem pulseFraction_le_one (tau : ℝ) : pulseFraction tau ≤ 1 := min_le_left 1 _

/-- On the interval where the expansions are stated the clamp is inactive. -/
theorem pulseFraction_eq_self {tau : ℝ} (h0 : 0 ≤ tau) (h1 : tau ≤ 1) :
    pulseFraction tau = tau := by
  rw [pulseFraction, max_eq_right h0, min_eq_right h1]

/-! ## Elementary bounds on the simplex -/

/-- A product of two differences of probabilities lies in `[-1,1]`.  This is the bound on the
quadratic cross term of the exact migration linkage law. -/
private theorem abs_probability_difference_product_le_one
    (firstLeft secondLeft firstRight secondRight : ℝ)
    (h1 : 0 ≤ firstLeft) (h2 : firstLeft ≤ 1) (h3 : 0 ≤ secondLeft) (h4 : secondLeft ≤ 1)
    (h5 : 0 ≤ firstRight) (h6 : firstRight ≤ 1) (h7 : 0 ≤ secondRight)
    (h8 : secondRight ≤ 1) :
    |(firstLeft - secondLeft) * (firstRight - secondRight)| ≤ 1 := by
  rw [abs_le]
  constructor <;>
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - (firstLeft - secondLeft))
        (by linarith : (0:ℝ) ≤ 1 + (firstRight - secondRight)),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 + (firstLeft - secondLeft))
        (by linarith : (0:ℝ) ≤ 1 - (firstRight - secondRight)),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 - (firstLeft - secondLeft))
        (by linarith : (0:ℝ) ≤ 1 - (firstRight - secondRight)),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 + (firstLeft - secondLeft))
        (by linarith : (0:ℝ) ≤ 1 + (firstRight - secondRight))]

/-- The exact migration linkage velocity is bounded by two on the simplex: two linkage
determinants of modulus at most a quarter and one probability-difference product. -/
theorem abs_migrationLinkageVelocity_le_two (source recipient : TwoLocusHaplotypeFrequencies) :
    |migrationLinkageVelocity source recipient| ≤ 2 := by
  have hcross := abs_probability_difference_product_le_one source.leftFrequency
    recipient.leftFrequency source.rightFrequency recipient.rightFrequency
    source.leftFrequency_nonneg source.leftFrequency_le_one
    recipient.leftFrequency_nonneg recipient.leftFrequency_le_one
    source.rightFrequency_nonneg source.rightFrequency_le_one
    recipient.rightFrequency_nonneg recipient.rightFrequency_le_one
  have hsource := source.linkage_abs_le_quarter
  have hrecipient := recipient.linkage_abs_le_quarter
  rw [abs_le] at hcross hsource hrecipient
  simp only [migrationLinkageVelocity]
  rw [abs_le]
  constructor <;> linarith [hcross.1, hcross.2, hsource.1, hsource.2, hrecipient.1,
    hrecipient.2]

/-- An exactly affine coordinate has vanishing second-order residual. -/
private theorem abs_affine_residual_le (value speed target : ℝ) (htarget : 0 ≤ target) :
    |value + speed - value - speed| ≤ target := by
  have hzero : value + speed - value - speed = 0 := by ring
  rw [hzero, abs_zero]
  exact htarget

/-- A coordinate that is exactly quadratic in the pulse fraction has its residual controlled
by the modulus of the quadratic coefficient. -/
private theorem abs_quadratic_residual_le (value speed cross bound tau : ℝ)
    (hcross : |cross| ≤ bound) :
    |value + tau * speed - tau ^ 2 * cross - value - tau * speed| ≤ bound * tau ^ 2 := by
  have hrw : value + tau * speed - tau ^ 2 * cross - value - tau * speed =
      -(tau ^ 2 * cross) := by ring
  have habs : |(-(tau ^ 2 * cross))| = tau ^ 2 * |cross| := by
    rw [abs_neg, abs_mul, abs_of_nonneg (sq_nonneg tau)]
  rw [hrw, habs]
  nlinarith [mul_nonneg (sq_nonneg tau) (sub_nonneg.mpr hcross)]

/-- The product residual bound behind the Leibniz rule for expansions. -/
private theorem abs_product_residual_le
    (firstValue secondValue firstSpeed secondSpeed firstImage secondImage
      firstBound secondBound firstSpeedBound secondSpeedBound
      firstError secondError tau : ℝ)
    (htau0 : 0 ≤ tau) (htau1 : tau ≤ 1)
    (hfirstValue : |firstValue| ≤ firstBound) (hsecondImage : |secondImage| ≤ secondBound)
    (hfirstSpeed : |firstSpeed| ≤ firstSpeedBound)
    (hsecondSpeed : |secondSpeed| ≤ secondSpeedBound)
    (hsecondError : 0 ≤ secondError)
    (hfirstExpansion : |firstImage - firstValue - tau * firstSpeed| ≤ firstError * tau ^ 2)
    (hsecondExpansion : |secondImage - secondValue - tau * secondSpeed| ≤
      secondError * tau ^ 2) :
    |firstImage * secondImage - firstValue * secondValue -
        tau * (firstValue * secondSpeed + secondValue * firstSpeed)| ≤
      (firstBound * secondError + firstSpeedBound * (secondSpeedBound + secondError) +
        firstError * secondBound) * tau ^ 2 := by
  have hfirstNonneg : 0 ≤ firstBound := le_trans (abs_nonneg _) hfirstValue
  have hsecondSpeedNonneg : 0 ≤ secondSpeedBound := le_trans (abs_nonneg _) hsecondSpeed
  have hkey : firstImage * secondImage - firstValue * secondValue -
      tau * (firstValue * secondSpeed + secondValue * firstSpeed) =
      firstValue * (secondImage - secondValue - tau * secondSpeed) +
        tau * firstSpeed * (secondImage - secondValue) +
        (firstImage - firstValue - tau * firstSpeed) * secondImage := by ring
  have htriangle := abs_add (secondImage - secondValue - tau * secondSpeed) (tau * secondSpeed)
  rw [show secondImage - secondValue - tau * secondSpeed + tau * secondSpeed =
    secondImage - secondValue from by ring] at htriangle
  have hspeedTerm : |tau * secondSpeed| ≤ secondSpeedBound * tau := by
    rw [abs_mul, abs_of_nonneg htau0, mul_comm]
    exact mul_le_mul_of_nonneg_right hsecondSpeed htau0
  have hsquare : secondError * tau ^ 2 ≤ secondError * tau := by
    nlinarith [mul_nonneg hsecondError (mul_nonneg htau0 (sub_nonneg.mpr htau1))]
  have hdifference : |secondImage - secondValue| ≤ (secondSpeedBound + secondError) * tau := by
    nlinarith [htriangle, hspeedTerm, hsquare, hsecondExpansion]
  have hfirstTerm : |firstValue * (secondImage - secondValue - tau * secondSpeed)| ≤
      firstBound * (secondError * tau ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul hfirstValue hsecondExpansion (abs_nonneg _) hfirstNonneg
  have hmiddleTerm : |tau * firstSpeed * (secondImage - secondValue)| ≤
      firstSpeedBound * tau * ((secondSpeedBound + secondError) * tau) := by
    rw [abs_mul]
    refine mul_le_mul ?_ hdifference (abs_nonneg _) (by positivity)
    rw [abs_mul, abs_of_nonneg htau0, mul_comm]
    exact mul_le_mul_of_nonneg_right hfirstSpeed htau0
  have hlastTerm : |(firstImage - firstValue - tau * firstSpeed) * secondImage| ≤
      firstError * tau ^ 2 * secondBound := by
    rw [abs_mul]
    exact mul_le_mul hfirstExpansion hsecondImage (abs_nonneg _)
      (le_trans (abs_nonneg _) hfirstExpansion)
  have hsum : |firstValue * (secondImage - secondValue - tau * secondSpeed) +
      tau * firstSpeed * (secondImage - secondValue) +
      (firstImage - firstValue - tau * firstSpeed) * secondImage| ≤
      |firstValue * (secondImage - secondValue - tau * secondSpeed)| +
        |tau * firstSpeed * (secondImage - secondValue)| +
        |(firstImage - firstValue - tau * firstSpeed) * secondImage| :=
    le_trans (abs_add _ _) (add_le_add_right (abs_add _ _) _)
  have hring : firstBound * (secondError * tau ^ 2) +
      firstSpeedBound * tau * ((secondSpeedBound + secondError) * tau) +
      firstError * tau ^ 2 * secondBound =
      (firstBound * secondError + firstSpeedBound * (secondSpeedBound + secondError) +
        firstError * secondBound) * tau ^ 2 := by ring
  rw [hkey]
  linarith

/-! ## The expansion certificate -/

/-- Second-order expansion certificate for one real observable of the deme state along a
one-parameter family of deterministic pulses.  `velocity` is the first-order coefficient,
`remainder` bounds the quadratic residual uniformly over the state space, and the two bound
fields record uniform sup-norm control of the observable and of its velocity, which the
Leibniz rule consumes.

Assumes: `pulse tau` maps the deme state space into itself for every real `tau`; the fields
are data supplied by the constructor, never existential claims. -/
structure PulseExpansion {D : ℕ}
    (pulse : ℝ → DemeHaplotypeState D → DemeHaplotypeState D)
    (observable : DemeHaplotypeState D → ℝ) where
  velocity : DemeHaplotypeState D → ℝ
  valueBound : ℝ
  velocityBound : ℝ
  remainder : ℝ
  value_abs_le : ∀ state, |observable state| ≤ valueBound
  velocity_abs_le : ∀ state, |velocity state| ≤ velocityBound
  expansion : ∀ tau, 0 ≤ tau → tau ≤ 1 → ∀ state,
    |observable (pulse tau state) - observable state - tau * velocity state| ≤
      remainder * tau ^ 2

/-- A concrete deme configuration, used to turn the uniform bounds of a `PulseExpansion` into
numerical nonnegativity facts. -/
def referenceState (D : ℕ) : DemeHaplotypeState D := fun _ ↦ maximalCoupling

namespace PulseExpansion

variable {D : ℕ} {pulse : ℝ → DemeHaplotypeState D → DemeHaplotypeState D}
  {observable : DemeHaplotypeState D → ℝ}

/-- A uniform bound on a real observable of a nonempty state space is nonnegative. -/
theorem valueBound_nonneg (certificate : PulseExpansion pulse observable) :
    0 ≤ certificate.valueBound :=
  le_trans (abs_nonneg _) (certificate.value_abs_le (referenceState D))

/-- The velocity bound of an expansion is nonnegative. -/
theorem velocityBound_nonneg (certificate : PulseExpansion pulse observable) :
    0 ≤ certificate.velocityBound :=
  le_trans (abs_nonneg _) (certificate.velocity_abs_le (referenceState D))

/-- The quadratic remainder of an expansion is nonnegative, read off at unit parameter. -/
theorem remainder_nonneg (certificate : PulseExpansion pulse observable) :
    0 ≤ certificate.remainder := by
  have hunit := certificate.expansion 1 zero_le_one le_rfl (referenceState D)
  rw [one_pow, mul_one] at hunit
  exact le_trans (abs_nonneg _) hunit

/-- Transport an expansion along a pointwise equality of observables. -/
def ofEq {other : DemeHaplotypeState D → ℝ} (certificate : PulseExpansion pulse observable)
    (hequal : ∀ state, observable state = other state) : PulseExpansion pulse other where
  velocity := certificate.velocity
  valueBound := certificate.valueBound
  velocityBound := certificate.velocityBound
  remainder := certificate.remainder
  value_abs_le state := by
    rw [← hequal state]
    exact certificate.value_abs_le state
  velocity_abs_le := certificate.velocity_abs_le
  expansion tau h0 h1 state := by
    rw [← hequal (pulse tau state), ← hequal state]
    exact certificate.expansion tau h0 h1 state

/-- A constant observable expands with zero velocity and no remainder. -/
def const (D : ℕ) (pulse : ℝ → DemeHaplotypeState D → DemeHaplotypeState D) (level : ℝ) :
    PulseExpansion pulse (fun _ ↦ level) where
  velocity _ := 0
  valueBound := |level|
  velocityBound := 0
  remainder := 0
  value_abs_le _ := le_rfl
  velocity_abs_le _ := by rw [abs_zero]
  expansion tau _ _ _ := by
    have hzero : level - level - tau * 0 = 0 := by ring
    rw [hzero, abs_zero, zero_mul]

/-- Expansions add coordinatewise. -/
def add {first second : DemeHaplotypeState D → ℝ}
    (firstCertificate : PulseExpansion pulse first)
    (secondCertificate : PulseExpansion pulse second) :
    PulseExpansion pulse (fun state ↦ first state + second state) where
  velocity state := firstCertificate.velocity state + secondCertificate.velocity state
  valueBound := firstCertificate.valueBound + secondCertificate.valueBound
  velocityBound := firstCertificate.velocityBound + secondCertificate.velocityBound
  remainder := firstCertificate.remainder + secondCertificate.remainder
  value_abs_le state :=
    le_trans (abs_add _ _)
      (add_le_add (firstCertificate.value_abs_le state) (secondCertificate.value_abs_le state))
  velocity_abs_le state :=
    le_trans (abs_add _ _)
      (add_le_add (firstCertificate.velocity_abs_le state)
        (secondCertificate.velocity_abs_le state))
  expansion tau h0 h1 state := by
    have hfirst := firstCertificate.expansion tau h0 h1 state
    have hsecond := secondCertificate.expansion tau h0 h1 state
    have hkey : first (pulse tau state) + second (pulse tau state) -
        (first state + second state) -
        tau * (firstCertificate.velocity state + secondCertificate.velocity state) =
        (first (pulse tau state) - first state - tau * firstCertificate.velocity state) +
          (second (pulse tau state) - second state -
            tau * secondCertificate.velocity state) := by ring
    have hring : firstCertificate.remainder * tau ^ 2 + secondCertificate.remainder * tau ^ 2 =
        (firstCertificate.remainder + secondCertificate.remainder) * tau ^ 2 := by ring
    rw [hkey]
    have htriangle := abs_add
      (first (pulse tau state) - first state - tau * firstCertificate.velocity state)
      (second (pulse tau state) - second state - tau * secondCertificate.velocity state)
    linarith

/-- Expansions are closed under real scalar multiples. -/
def smul {first : DemeHaplotypeState D → ℝ} (scalar : ℝ)
    (firstCertificate : PulseExpansion pulse first) :
    PulseExpansion pulse (fun state ↦ scalar * first state) where
  velocity state := scalar * firstCertificate.velocity state
  valueBound := |scalar| * firstCertificate.valueBound
  velocityBound := |scalar| * firstCertificate.velocityBound
  remainder := |scalar| * firstCertificate.remainder
  value_abs_le state := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (firstCertificate.value_abs_le state) (abs_nonneg scalar)
  velocity_abs_le state := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (firstCertificate.velocity_abs_le state) (abs_nonneg scalar)
  expansion tau h0 h1 state := by
    have hfirst := firstCertificate.expansion tau h0 h1 state
    have hkey : scalar * first (pulse tau state) - scalar * first state -
        tau * (scalar * firstCertificate.velocity state) =
        scalar * (first (pulse tau state) - first state -
          tau * firstCertificate.velocity state) := by ring
    have hring : |scalar| * (firstCertificate.remainder * tau ^ 2) =
        |scalar| * firstCertificate.remainder * tau ^ 2 := by ring
    rw [hkey, abs_mul, ← hring]
    exact mul_le_mul_of_nonneg_left hfirst (abs_nonneg scalar)

/-- The Leibniz rule: the velocity of a product is `f v_g + g v_f`, and the remainder is
assembled from the uniform bounds of the two factors. -/
def mul {first second : DemeHaplotypeState D → ℝ}
    (firstCertificate : PulseExpansion pulse first)
    (secondCertificate : PulseExpansion pulse second) :
    PulseExpansion pulse (fun state ↦ first state * second state) where
  velocity state := first state * secondCertificate.velocity state +
    second state * firstCertificate.velocity state
  valueBound := firstCertificate.valueBound * secondCertificate.valueBound
  velocityBound := firstCertificate.valueBound * secondCertificate.velocityBound +
    secondCertificate.valueBound * firstCertificate.velocityBound
  remainder := firstCertificate.valueBound * secondCertificate.remainder +
    firstCertificate.velocityBound *
      (secondCertificate.velocityBound + secondCertificate.remainder) +
    firstCertificate.remainder * secondCertificate.valueBound
  value_abs_le state := by
    rw [abs_mul]
    exact mul_le_mul (firstCertificate.value_abs_le state)
      (secondCertificate.value_abs_le state) (abs_nonneg _) firstCertificate.valueBound_nonneg
  velocity_abs_le state := by
    refine le_trans (abs_add _ _) (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul (firstCertificate.value_abs_le state)
        (secondCertificate.velocity_abs_le state) (abs_nonneg _)
        firstCertificate.valueBound_nonneg
    · rw [abs_mul]
      exact mul_le_mul (secondCertificate.value_abs_le state)
        (firstCertificate.velocity_abs_le state) (abs_nonneg _)
        secondCertificate.valueBound_nonneg
  expansion tau h0 h1 state :=
    abs_product_residual_le (first state) (second state) (firstCertificate.velocity state)
      (secondCertificate.velocity state) (first (pulse tau state)) (second (pulse tau state))
      firstCertificate.valueBound secondCertificate.valueBound
      firstCertificate.velocityBound secondCertificate.velocityBound
      firstCertificate.remainder secondCertificate.remainder tau h0 h1
      (firstCertificate.value_abs_le state) (secondCertificate.value_abs_le _)
      (firstCertificate.velocity_abs_le state) (secondCertificate.velocity_abs_le state)
      secondCertificate.remainder_nonneg (firstCertificate.expansion tau h0 h1 state)
      (secondCertificate.expansion tau h0 h1 state)

end PulseExpansion

/-- The three base coordinate expansions of one pulse family, from which every member of the
closed low-order family is assembled by the four closure operations: the two marginal allele
frequencies and the linkage determinant of each deme. -/
structure PulseCoordinateExpansion {D : ℕ}
    (pulse : ℝ → DemeHaplotypeState D → DemeHaplotypeState D) where
  leftMarginal : ∀ index : Fin D,
    PulseExpansion pulse (fun state ↦ (state index).leftFrequency)
  rightMarginal : ∀ index : Fin D,
    PulseExpansion pulse (fun state ↦ (state index).rightFrequency)
  linkageDeterminant : ∀ index : Fin D,
    PulseExpansion pulse (fun state ↦ (state index).linkage)

/-! ## The three deterministic pulse families -/

/-- One deterministic haplotype migration pulse.  Only the recipient deme changes, and it
receives the clamped fraction of the source deme's haplotype vector; the corpus's `mixture`
retains arbitrary linkage in both populations. -/
def migrationPulse {D : ℕ} (source recipient : Fin D) (tau : ℝ)
    (state : DemeHaplotypeState D) : DemeHaplotypeState D := fun index ↦
  if index = recipient then
    mixture (pulseFraction tau) (pulseFraction_nonneg tau) (pulseFraction_le_one tau)
      (state source) (state recipient)
  else state index

/-- One recombination pulse in a single deme: the clamped fraction is redrawn from the
product of that deme's two marginal allele laws. -/
def recombinationPulseAt {D : ℕ} (target : Fin D) (tau : ℝ)
    (state : DemeHaplotypeState D) : DemeHaplotypeState D := fun index ↦
  if index = target then
    recombinationPulse (pulseFraction tau) (pulseFraction_nonneg tau)
      (pulseFraction_le_one tau) (state target)
  else state index

/-- One symmetric allele-flip mutation pulse at the left locus of a single deme. -/
def leftMutationPulseAt {D : ℕ} (target : Fin D) (tau : ℝ)
    (state : DemeHaplotypeState D) : DemeHaplotypeState D := fun index ↦
  if index = target then
    leftMutationPulse (pulseFraction tau) (pulseFraction_nonneg tau)
      (pulseFraction_le_one tau) (state target)
  else state index

/-- One symmetric allele-flip mutation pulse at the right locus of a single deme. -/
def rightMutationPulseAt {D : ℕ} (target : Fin D) (tau : ℝ)
    (state : DemeHaplotypeState D) : DemeHaplotypeState D := fun index ↦
  if index = target then
    rightMutationPulse (pulseFraction tau) (pulseFraction_nonneg tau)
      (pulseFraction_le_one tau) (state target)
  else state index

/-! ## Exact pointwise laws of the single-deme mutation pulses -/

/-- The left marginal allele frequency moves by the centered left contrast under a left-locus
mutation pulse.  This is the frequency form of the corpus's contrast retention law. -/
theorem leftMutationPulse_leftFrequency (epsilon : ℝ) (h0 : 0 ≤ epsilon) (h1 : epsilon ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (leftMutationPulse epsilon h0 h1 frequency).leftFrequency =
      frequency.leftFrequency + epsilon * frequency.leftContrast := by
  simp only [leftMutationPulse, mixture_leftFrequency, leftAlleleFlip_leftFrequency,
    leftContrast]
  ring

/-- A left-locus mutation pulse leaves the right marginal allele frequency alone. -/
theorem leftMutationPulse_rightFrequency (epsilon : ℝ) (h0 : 0 ≤ epsilon) (h1 : epsilon ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (leftMutationPulse epsilon h0 h1 frequency).rightFrequency = frequency.rightFrequency := by
  simp only [leftMutationPulse, mixture_rightFrequency, leftAlleleFlip_rightFrequency]
  ring

/-- The right marginal allele frequency moves by the centered right contrast under a
right-locus mutation pulse. -/
theorem rightMutationPulse_rightFrequency (epsilon : ℝ) (h0 : 0 ≤ epsilon) (h1 : epsilon ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (rightMutationPulse epsilon h0 h1 frequency).rightFrequency =
      frequency.rightFrequency + epsilon * frequency.rightContrast := by
  simp only [rightMutationPulse, mixture_rightFrequency, rightAlleleFlip_rightFrequency,
    rightContrast]
  ring

/-- A right-locus mutation pulse leaves the left marginal allele frequency alone. -/
theorem rightMutationPulse_leftFrequency (epsilon : ℝ) (h0 : 0 ≤ epsilon) (h1 : epsilon ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (rightMutationPulse epsilon h0 h1 frequency).leftFrequency = frequency.leftFrequency := by
  simp only [rightMutationPulse, mixture_leftFrequency, rightAlleleFlip_leftFrequency]
  ring

/-! ## Exact pointwise laws of the pulses on the deme state -/

/-- Left marginal frequencies are exactly affine in the migration fraction. -/
theorem migrationPulse_leftFrequency {D : ℕ} (source recipient index : Fin D) {tau : ℝ}
    (h0 : 0 ≤ tau) (h1 : tau ≤ 1) (state : DemeHaplotypeState D) :
    (migrationPulse source recipient tau state index).leftFrequency =
      (state index).leftFrequency +
        tau * (if index = recipient then
          (state source).leftFrequency - (state recipient).leftFrequency else 0) := by
  by_cases hindex : index = recipient
  · have himage : migrationPulse source recipient tau state index =
        mixture (pulseFraction tau) (pulseFraction_nonneg tau) (pulseFraction_le_one tau)
          (state source) (state recipient) := by
      simp [migrationPulse, hindex]
    rw [himage, mixture_leftFrequency, pulseFraction_eq_self h0 h1, if_pos hindex, hindex]
    ring
  · have himage : migrationPulse source recipient tau state index = state index := by
      simp [migrationPulse, hindex]
    rw [himage, if_neg hindex]
    ring

/-- Right marginal frequencies are exactly affine in the migration fraction. -/
theorem migrationPulse_rightFrequency {D : ℕ} (source recipient index : Fin D) {tau : ℝ}
    (h0 : 0 ≤ tau) (h1 : tau ≤ 1) (state : DemeHaplotypeState D) :
    (migrationPulse source recipient tau state index).rightFrequency =
      (state index).rightFrequency +
        tau * (if index = recipient then
          (state source).rightFrequency - (state recipient).rightFrequency else 0) := by
  by_cases hindex : index = recipient
  · have himage : migrationPulse source recipient tau state index =
        mixture (pulseFraction tau) (pulseFraction_nonneg tau) (pulseFraction_le_one tau)
          (state source) (state recipient) := by
      simp [migrationPulse, hindex]
    rw [himage, mixture_rightFrequency, pulseFraction_eq_self h0 h1, if_pos hindex, hindex]
    ring
  · have himage : migrationPulse source recipient tau state index = state index := by
      simp [migrationPulse, hindex]
    rw [himage, if_neg hindex]
    ring

/-- The exact quadratic migration law for the linkage determinant, transported to the deme
state.  The first-order coefficient is the corpus's `migrationLinkageVelocity` and the second
is the joint differentiation term of the two marginals. -/
theorem migrationPulse_linkage {D : ℕ} (source recipient index : Fin D) {tau : ℝ}
    (h0 : 0 ≤ tau) (h1 : tau ≤ 1) (state : DemeHaplotypeState D) :
    (migrationPulse source recipient tau state index).linkage =
      (state index).linkage +
        tau * (if index = recipient then
          migrationLinkageVelocity (state source) (state recipient) else 0) -
        tau ^ 2 * (if index = recipient then
          ((state source).leftFrequency - (state recipient).leftFrequency) *
            ((state source).rightFrequency - (state recipient).rightFrequency) else 0) := by
  by_cases hindex : index = recipient
  · have himage : migrationPulse source recipient tau state index =
        mixture (pulseFraction tau) (pulseFraction_nonneg tau) (pulseFraction_le_one tau)
          (state source) (state recipient) := by
      simp [migrationPulse, hindex]
    rw [himage, mixture_linkage_eq_velocity, pulseFraction_eq_self h0 h1, if_pos hindex,
      if_pos hindex, hindex]
    ring
  · have himage : migrationPulse source recipient tau state index = state index := by
      simp [migrationPulse, hindex]
    rw [himage, if_neg hindex, if_neg hindex]
    ring

/-- Recombination changes no marginal allele frequency at the left locus. -/
theorem recombinationPulseAt_leftFrequency {D : ℕ} (target index : Fin D) (tau : ℝ)
    (state : DemeHaplotypeState D) :
    (recombinationPulseAt target tau state index).leftFrequency =
      (state index).leftFrequency + tau * 0 := by
  by_cases hindex : index = target
  · have himage : recombinationPulseAt target tau state index =
        recombinationPulse (pulseFraction tau) (pulseFraction_nonneg tau)
          (pulseFraction_le_one tau) (state target) := by
      simp [recombinationPulseAt, hindex]
    rw [himage, recombinationPulse_leftFrequency, hindex]
    ring
  · have himage : recombinationPulseAt target tau state index = state index := by
      simp [recombinationPulseAt, hindex]
    rw [himage]
    ring

/-- Recombination changes no marginal allele frequency at the right locus. -/
theorem recombinationPulseAt_rightFrequency {D : ℕ} (target index : Fin D) (tau : ℝ)
    (state : DemeHaplotypeState D) :
    (recombinationPulseAt target tau state index).rightFrequency =
      (state index).rightFrequency + tau * 0 := by
  by_cases hindex : index = target
  · have himage : recombinationPulseAt target tau state index =
        recombinationPulse (pulseFraction tau) (pulseFraction_nonneg tau)
          (pulseFraction_le_one tau) (state target) := by
      simp [recombinationPulseAt, hindex]
    rw [himage, recombinationPulse_rightFrequency, hindex]
    ring
  · have himage : recombinationPulseAt target tau state index = state index := by
      simp [recombinationPulseAt, hindex]
    rw [himage]
    ring

/-- A recombination pulse retains exactly the complementary fraction of linkage, so the
linkage determinant is exactly affine in the fraction with the corpus's recombination
velocity. -/
theorem recombinationPulseAt_linkage {D : ℕ} (target index : Fin D) {tau : ℝ}
    (h0 : 0 ≤ tau) (h1 : tau ≤ 1) (state : DemeHaplotypeState D) :
    (recombinationPulseAt target tau state index).linkage =
      (state index).linkage +
        tau * (if index = target then recombinationLinkageVelocity (state target) else 0) := by
  by_cases hindex : index = target
  · have himage : recombinationPulseAt target tau state index =
        recombinationPulse (pulseFraction tau) (pulseFraction_nonneg tau)
          (pulseFraction_le_one tau) (state target) := by
      simp [recombinationPulseAt, hindex]
    rw [himage, recombinationPulse_linkage, pulseFraction_eq_self h0 h1, if_pos hindex, hindex]
    simp only [recombinationLinkageVelocity]
    ring
  · have himage : recombinationPulseAt target tau state index = state index := by
      simp [recombinationPulseAt, hindex]
    rw [himage, if_neg hindex]
    ring

/-- Left-locus mutation moves the left marginal by the centered left contrast. -/
theorem leftMutationPulseAt_leftFrequency {D : ℕ} (target index : Fin D) {tau : ℝ}
    (h0 : 0 ≤ tau) (h1 : tau ≤ 1) (state : DemeHaplotypeState D) :
    (leftMutationPulseAt target tau state index).leftFrequency =
      (state index).leftFrequency +
        tau * (if index = target then (state target).leftContrast else 0) := by
  by_cases hindex : index = target
  · have himage : leftMutationPulseAt target tau state index =
        leftMutationPulse (pulseFraction tau) (pulseFraction_nonneg tau)
          (pulseFraction_le_one tau) (state target) := by
      simp [leftMutationPulseAt, hindex]
    rw [himage, leftMutationPulse_leftFrequency, pulseFraction_eq_self h0 h1, if_pos hindex,
      hindex]
  · have himage : leftMutationPulseAt target tau state index = state index := by
      simp [leftMutationPulseAt, hindex]
    rw [himage, if_neg hindex]
    ring

/-- Left-locus mutation leaves every right marginal alone. -/
theorem leftMutationPulseAt_rightFrequency {D : ℕ} (target index : Fin D) (tau : ℝ)
    (state : DemeHaplotypeState D) :
    (leftMutationPulseAt target tau state index).rightFrequency =
      (state index).rightFrequency + tau * 0 := by
  by_cases hindex : index = target
  · have himage : leftMutationPulseAt target tau state index =
        leftMutationPulse (pulseFraction tau) (pulseFraction_nonneg tau)
          (pulseFraction_le_one tau) (state target) := by
      simp [leftMutationPulseAt, hindex]
    rw [himage, leftMutationPulse_rightFrequency, hindex]
    ring
  · have himage : leftMutationPulseAt target tau state index = state index := by
      simp [leftMutationPulseAt, hindex]
    rw [himage]
    ring

/-- A single-locus mutation pulse retains exactly `1 - 2 epsilon` of linkage, so the linkage
determinant is exactly affine with velocity `-2 D`. -/
theorem leftMutationPulseAt_linkage {D : ℕ} (target index : Fin D) {tau : ℝ}
    (h0 : 0 ≤ tau) (h1 : tau ≤ 1) (state : DemeHaplotypeState D) :
    (leftMutationPulseAt target tau state index).linkage =
      (state index).linkage +
        tau * (if index = target then -2 * (state target).linkage else 0) := by
  by_cases hindex : index = target
  · have himage : leftMutationPulseAt target tau state index =
        leftMutationPulse (pulseFraction tau) (pulseFraction_nonneg tau)
          (pulseFraction_le_one tau) (state target) := by
      simp [leftMutationPulseAt, hindex]
    rw [himage, leftMutationPulse_linkage, pulseFraction_eq_self h0 h1, if_pos hindex, hindex]
    ring
  · have himage : leftMutationPulseAt target tau state index = state index := by
      simp [leftMutationPulseAt, hindex]
    rw [himage, if_neg hindex]
    ring

/-- Right-locus mutation moves the right marginal by the centered right contrast. -/
theorem rightMutationPulseAt_rightFrequency {D : ℕ} (target index : Fin D) {tau : ℝ}
    (h0 : 0 ≤ tau) (h1 : tau ≤ 1) (state : DemeHaplotypeState D) :
    (rightMutationPulseAt target tau state index).rightFrequency =
      (state index).rightFrequency +
        tau * (if index = target then (state target).rightContrast else 0) := by
  by_cases hindex : index = target
  · have himage : rightMutationPulseAt target tau state index =
        rightMutationPulse (pulseFraction tau) (pulseFraction_nonneg tau)
          (pulseFraction_le_one tau) (state target) := by
      simp [rightMutationPulseAt, hindex]
    rw [himage, rightMutationPulse_rightFrequency, pulseFraction_eq_self h0 h1, if_pos hindex,
      hindex]
  · have himage : rightMutationPulseAt target tau state index = state index := by
      simp [rightMutationPulseAt, hindex]
    rw [himage, if_neg hindex]
    ring

/-- Right-locus mutation leaves every left marginal alone. -/
theorem rightMutationPulseAt_leftFrequency {D : ℕ} (target index : Fin D) (tau : ℝ)
    (state : DemeHaplotypeState D) :
    (rightMutationPulseAt target tau state index).leftFrequency =
      (state index).leftFrequency + tau * 0 := by
  by_cases hindex : index = target
  · have himage : rightMutationPulseAt target tau state index =
        rightMutationPulse (pulseFraction tau) (pulseFraction_nonneg tau)
          (pulseFraction_le_one tau) (state target) := by
      simp [rightMutationPulseAt, hindex]
    rw [himage, rightMutationPulse_leftFrequency, hindex]
    ring
  · have himage : rightMutationPulseAt target tau state index = state index := by
      simp [rightMutationPulseAt, hindex]
    rw [himage]
    ring

/-- The right-locus mutation pulse damps linkage at the same rate as the left-locus one. -/
theorem rightMutationPulseAt_linkage {D : ℕ} (target index : Fin D) {tau : ℝ}
    (h0 : 0 ≤ tau) (h1 : tau ≤ 1) (state : DemeHaplotypeState D) :
    (rightMutationPulseAt target tau state index).linkage =
      (state index).linkage +
        tau * (if index = target then -2 * (state target).linkage else 0) := by
  by_cases hindex : index = target
  · have himage : rightMutationPulseAt target tau state index =
        rightMutationPulse (pulseFraction tau) (pulseFraction_nonneg tau)
          (pulseFraction_le_one tau) (state target) := by
      simp [rightMutationPulseAt, hindex]
    rw [himage, rightMutationPulse_linkage, pulseFraction_eq_self h0 h1, if_pos hindex, hindex]
    ring
  · have himage : rightMutationPulseAt target tau state index = state index := by
      simp [rightMutationPulseAt, hindex]
    rw [himage, if_neg hindex]
    ring

/-! ## Base expansions of the three deme coordinates under each pulse -/

/-- Uniform bound on a marginal allele frequency of any deme. -/
private theorem abs_leftFrequency_le_one {D : ℕ} (state : DemeHaplotypeState D)
    (index : Fin D) : |(state index).leftFrequency| ≤ 1 := by
  rw [abs_le]
  exact ⟨by linarith [(state index).leftFrequency_nonneg], (state index).leftFrequency_le_one⟩

/-- Uniform bound on a right marginal allele frequency of any deme. -/
private theorem abs_rightFrequency_le_one {D : ℕ} (state : DemeHaplotypeState D)
    (index : Fin D) : |(state index).rightFrequency| ≤ 1 := by
  rw [abs_le]
  exact ⟨by linarith [(state index).rightFrequency_nonneg], (state index).rightFrequency_le_one⟩

/-- The left marginal of any deme under a migration pulse. -/
def migrationLeftExpansion {D : ℕ} (source recipient index : Fin D) :
    PulseExpansion (migrationPulse source recipient)
      (fun state ↦ (state index).leftFrequency) where
  velocity state := if index = recipient then
    (state source).leftFrequency - (state recipient).leftFrequency else 0
  valueBound := 1
  velocityBound := 1
  remainder := 0
  value_abs_le state := abs_leftFrequency_le_one state index
  velocity_abs_le state := by
    by_cases hindex : index = recipient
    · rw [if_pos hindex, abs_le]
      constructor
      · linarith [(state source).leftFrequency_nonneg, (state recipient).leftFrequency_le_one]
      · linarith [(state source).leftFrequency_le_one, (state recipient).leftFrequency_nonneg]
    · rw [if_neg hindex, abs_zero]
      norm_num
  expansion tau h0 h1 state := by
    rw [migrationPulse_leftFrequency source recipient index h0 h1 state]
    exact abs_affine_residual_le _ _ _ (by norm_num)

/-- The right marginal of any deme under a migration pulse. -/
def migrationRightExpansion {D : ℕ} (source recipient index : Fin D) :
    PulseExpansion (migrationPulse source recipient)
      (fun state ↦ (state index).rightFrequency) where
  velocity state := if index = recipient then
    (state source).rightFrequency - (state recipient).rightFrequency else 0
  valueBound := 1
  velocityBound := 1
  remainder := 0
  value_abs_le state := abs_rightFrequency_le_one state index
  velocity_abs_le state := by
    by_cases hindex : index = recipient
    · rw [if_pos hindex, abs_le]
      constructor
      · linarith [(state source).rightFrequency_nonneg, (state recipient).rightFrequency_le_one]
      · linarith [(state source).rightFrequency_le_one, (state recipient).rightFrequency_nonneg]
    · rw [if_neg hindex, abs_zero]
      norm_num
  expansion tau h0 h1 state := by
    rw [migrationPulse_rightFrequency source recipient index h0 h1 state]
    exact abs_affine_residual_le _ _ _ (by norm_num)

/-- The linkage determinant of any deme under a migration pulse.  This is the only stage
coordinate with a nonzero quadratic remainder. -/
def migrationLinkageExpansion {D : ℕ} (source recipient index : Fin D) :
    PulseExpansion (migrationPulse source recipient)
      (fun state ↦ (state index).linkage) where
  velocity state := if index = recipient then
    migrationLinkageVelocity (state source) (state recipient) else 0
  valueBound := 1 / 4
  velocityBound := 2
  remainder := 1
  value_abs_le state := (state index).linkage_abs_le_quarter
  velocity_abs_le state := by
    by_cases hindex : index = recipient
    · rw [if_pos hindex]
      exact abs_migrationLinkageVelocity_le_two (state source) (state recipient)
    · rw [if_neg hindex, abs_zero]
      norm_num
  expansion tau h0 h1 state := by
    rw [migrationPulse_linkage source recipient index h0 h1 state]
    refine abs_quadratic_residual_le _ _ _ _ tau ?_
    by_cases hindex : index = recipient
    · rw [if_pos hindex]
      exact abs_probability_difference_product_le_one _ _ _ _
        (state source).leftFrequency_nonneg (state source).leftFrequency_le_one
        (state recipient).leftFrequency_nonneg (state recipient).leftFrequency_le_one
        (state source).rightFrequency_nonneg (state source).rightFrequency_le_one
        (state recipient).rightFrequency_nonneg (state recipient).rightFrequency_le_one
    · rw [if_neg hindex, abs_zero]
      norm_num

/-- The base coordinate expansions of a migration pulse. -/
def migrationCoordinateExpansion {D : ℕ} (source recipient : Fin D) :
    PulseCoordinateExpansion (migrationPulse source recipient) where
  leftMarginal := migrationLeftExpansion source recipient
  rightMarginal := migrationRightExpansion source recipient
  linkageDeterminant := migrationLinkageExpansion source recipient

/-- Uniform bound on a centered left-locus allele contrast. -/
private theorem abs_leftContrast_le_one (frequency : TwoLocusHaplotypeFrequencies) :
    |frequency.leftContrast| ≤ 1 := by
  simp only [leftContrast]
  rw [abs_le]
  exact ⟨by linarith [frequency.leftFrequency_le_one],
    by linarith [frequency.leftFrequency_nonneg]⟩

/-- Uniform bound on a centered right-locus allele contrast. -/
private theorem abs_rightContrast_le_one (frequency : TwoLocusHaplotypeFrequencies) :
    |frequency.rightContrast| ≤ 1 := by
  simp only [rightContrast]
  rw [abs_le]
  exact ⟨by linarith [frequency.rightFrequency_le_one],
    by linarith [frequency.rightFrequency_nonneg]⟩

/-- Uniform bound on the mutation damping velocity of the linkage determinant. -/
private theorem abs_two_linkage_le_half (frequency : TwoLocusHaplotypeFrequencies) :
    |(-2) * frequency.linkage| ≤ 1 / 2 := by
  have hquarter := frequency.linkage_abs_le_quarter
  rw [abs_le] at hquarter ⊢
  constructor <;> linarith [hquarter.1, hquarter.2]

/-- Uniform bound on the recombination velocity of the linkage determinant. -/
private theorem abs_recombinationLinkageVelocity_le_quarter
    (frequency : TwoLocusHaplotypeFrequencies) :
    |recombinationLinkageVelocity frequency| ≤ 1 / 4 := by
  simp only [recombinationLinkageVelocity]
  rw [abs_neg]
  exact frequency.linkage_abs_le_quarter

/-- The left marginal of any deme is fixed by a recombination pulse. -/
def recombinationLeftExpansion {D : ℕ} (target index : Fin D) :
    PulseExpansion (recombinationPulseAt target)
      (fun state ↦ (state index).leftFrequency) where
  velocity _ := 0
  valueBound := 1
  velocityBound := 0
  remainder := 0
  value_abs_le state := abs_leftFrequency_le_one state index
  velocity_abs_le _ := by rw [abs_zero]
  expansion tau _ _ state := by
    rw [recombinationPulseAt_leftFrequency target index tau state]
    exact abs_affine_residual_le _ _ _ (by norm_num)

/-- The right marginal of any deme is fixed by a recombination pulse. -/
def recombinationRightExpansion {D : ℕ} (target index : Fin D) :
    PulseExpansion (recombinationPulseAt target)
      (fun state ↦ (state index).rightFrequency) where
  velocity _ := 0
  valueBound := 1
  velocityBound := 0
  remainder := 0
  value_abs_le state := abs_rightFrequency_le_one state index
  velocity_abs_le _ := by rw [abs_zero]
  expansion tau _ _ state := by
    rw [recombinationPulseAt_rightFrequency target index tau state]
    exact abs_affine_residual_le _ _ _ (by norm_num)

/-- The linkage determinant decays exactly linearly in the recombination fraction. -/
def recombinationLinkageExpansion {D : ℕ} (target index : Fin D) :
    PulseExpansion (recombinationPulseAt target) (fun state ↦ (state index).linkage) where
  velocity state := if index = target then recombinationLinkageVelocity (state target) else 0
  valueBound := 1 / 4
  velocityBound := 1 / 4
  remainder := 0
  value_abs_le state := (state index).linkage_abs_le_quarter
  velocity_abs_le state := by
    by_cases hindex : index = target
    · rw [if_pos hindex]
      exact abs_recombinationLinkageVelocity_le_quarter (state target)
    · rw [if_neg hindex, abs_zero]
      norm_num
  expansion tau h0 h1 state := by
    rw [recombinationPulseAt_linkage target index h0 h1 state]
    exact abs_affine_residual_le _ _ _ (by norm_num)

/-- The base coordinate expansions of a recombination pulse. -/
def recombinationCoordinateExpansion {D : ℕ} (target : Fin D) :
    PulseCoordinateExpansion (recombinationPulseAt target) where
  leftMarginal := recombinationLeftExpansion target
  rightMarginal := recombinationRightExpansion target
  linkageDeterminant := recombinationLinkageExpansion target

/-- The left marginal under a left-locus mutation pulse moves by the centered contrast. -/
def leftMutationLeftExpansion {D : ℕ} (target index : Fin D) :
    PulseExpansion (leftMutationPulseAt target)
      (fun state ↦ (state index).leftFrequency) where
  velocity state := if index = target then (state target).leftContrast else 0
  valueBound := 1
  velocityBound := 1
  remainder := 0
  value_abs_le state := abs_leftFrequency_le_one state index
  velocity_abs_le state := by
    by_cases hindex : index = target
    · rw [if_pos hindex]
      exact abs_leftContrast_le_one (state target)
    · rw [if_neg hindex, abs_zero]
      norm_num
  expansion tau h0 h1 state := by
    rw [leftMutationPulseAt_leftFrequency target index h0 h1 state]
    exact abs_affine_residual_le _ _ _ (by norm_num)

/-- The right marginal is fixed by a left-locus mutation pulse. -/
def leftMutationRightExpansion {D : ℕ} (target index : Fin D) :
    PulseExpansion (leftMutationPulseAt target)
      (fun state ↦ (state index).rightFrequency) where
  velocity _ := 0
  valueBound := 1
  velocityBound := 0
  remainder := 0
  value_abs_le state := abs_rightFrequency_le_one state index
  velocity_abs_le _ := by rw [abs_zero]
  expansion tau _ _ state := by
    rw [leftMutationPulseAt_rightFrequency target index tau state]
    exact abs_affine_residual_le _ _ _ (by norm_num)

/-- The linkage determinant decays exactly linearly under a left-locus mutation pulse. -/
def leftMutationLinkageExpansion {D : ℕ} (target index : Fin D) :
    PulseExpansion (leftMutationPulseAt target) (fun state ↦ (state index).linkage) where
  velocity state := if index = target then (-2) * (state target).linkage else 0
  valueBound := 1 / 4
  velocityBound := 1 / 2
  remainder := 0
  value_abs_le state := (state index).linkage_abs_le_quarter
  velocity_abs_le state := by
    by_cases hindex : index = target
    · rw [if_pos hindex]
      exact abs_two_linkage_le_half (state target)
    · rw [if_neg hindex, abs_zero]
      norm_num
  expansion tau h0 h1 state := by
    rw [leftMutationPulseAt_linkage target index h0 h1 state]
    exact abs_affine_residual_le _ _ _ (by norm_num)

/-- The base coordinate expansions of a left-locus mutation pulse. -/
def leftMutationCoordinateExpansion {D : ℕ} (target : Fin D) :
    PulseCoordinateExpansion (leftMutationPulseAt target) where
  leftMarginal := leftMutationLeftExpansion target
  rightMarginal := leftMutationRightExpansion target
  linkageDeterminant := leftMutationLinkageExpansion target

/-- The left marginal is fixed by a right-locus mutation pulse. -/
def rightMutationLeftExpansion {D : ℕ} (target index : Fin D) :
    PulseExpansion (rightMutationPulseAt target)
      (fun state ↦ (state index).leftFrequency) where
  velocity _ := 0
  valueBound := 1
  velocityBound := 0
  remainder := 0
  value_abs_le state := abs_leftFrequency_le_one state index
  velocity_abs_le _ := by rw [abs_zero]
  expansion tau _ _ state := by
    rw [rightMutationPulseAt_leftFrequency target index tau state]
    exact abs_affine_residual_le _ _ _ (by norm_num)

/-- The right marginal under a right-locus mutation pulse moves by the centered contrast. -/
def rightMutationRightExpansion {D : ℕ} (target index : Fin D) :
    PulseExpansion (rightMutationPulseAt target)
      (fun state ↦ (state index).rightFrequency) where
  velocity state := if index = target then (state target).rightContrast else 0
  valueBound := 1
  velocityBound := 1
  remainder := 0
  value_abs_le state := abs_rightFrequency_le_one state index
  velocity_abs_le state := by
    by_cases hindex : index = target
    · rw [if_pos hindex]
      exact abs_rightContrast_le_one (state target)
    · rw [if_neg hindex, abs_zero]
      norm_num
  expansion tau h0 h1 state := by
    rw [rightMutationPulseAt_rightFrequency target index h0 h1 state]
    exact abs_affine_residual_le _ _ _ (by norm_num)

/-- The linkage determinant decays exactly linearly under a right-locus mutation pulse. -/
def rightMutationLinkageExpansion {D : ℕ} (target index : Fin D) :
    PulseExpansion (rightMutationPulseAt target) (fun state ↦ (state index).linkage) where
  velocity state := if index = target then (-2) * (state target).linkage else 0
  valueBound := 1 / 4
  velocityBound := 1 / 2
  remainder := 0
  value_abs_le state := (state index).linkage_abs_le_quarter
  velocity_abs_le state := by
    by_cases hindex : index = target
    · rw [if_pos hindex]
      exact abs_two_linkage_le_half (state target)
    · rw [if_neg hindex, abs_zero]
      norm_num
  expansion tau h0 h1 state := by
    rw [rightMutationPulseAt_linkage target index h0 h1 state]
    exact abs_affine_residual_le _ _ _ (by norm_num)

/-- The base coordinate expansions of a right-locus mutation pulse. -/
def rightMutationCoordinateExpansion {D : ℕ} (target : Fin D) :
    PulseCoordinateExpansion (rightMutationPulseAt target) where
  leftMarginal := rightMutationLeftExpansion target
  rightMarginal := rightMutationRightExpansion target
  linkageDeterminant := rightMutationLinkageExpansion target

/-! ## Every low-order coordinate expands under every pulse -/

namespace PulseCoordinateExpansion

variable {D : ℕ} {pulse : ℝ → DemeHaplotypeState D → DemeHaplotypeState D}

/-- Cross-deme left heterozygosity, assembled from the two left marginals by the Leibniz
rule. -/
def leftHeterozygosity (base : PulseCoordinateExpansion pulse) (first second : Fin D) :
    PulseExpansion pulse (twoLocusHJet first second).value :=
  PulseExpansion.ofEq
    (((base.leftMarginal first).mul
        ((PulseExpansion.const D pulse 1).add ((base.leftMarginal second).smul (-1)))).add
      ((base.leftMarginal second).mul
        ((PulseExpansion.const D pulse 1).add ((base.leftMarginal first).smul (-1)))))
    (fun _ ↦ rfl)

/-- Cross-deme right-locus heterozygosity, the coordinate family that NOTE1 equation (6)
adds to the stored low-order state. -/
def rightHeterozygosity (base : PulseCoordinateExpansion pulse) (first second : Fin D) :
    PulseExpansion pulse (twoLocusRightHJet first second).value :=
  PulseExpansion.ofEq
    (((base.rightMarginal first).mul
        ((PulseExpansion.const D pulse 1).add ((base.rightMarginal second).smul (-1)))).add
      ((base.rightMarginal second).mul
        ((PulseExpansion.const D pulse 1).add ((base.rightMarginal first).smul (-1)))))
    (fun _ ↦ rfl)

/-- The cross-deme product of linkage determinants. -/
def linkageProduct (base : PulseCoordinateExpansion pulse) (first second : Fin D) :
    PulseExpansion pulse (twoLocusDDJet first second).value :=
  PulseExpansion.ofEq
    ((base.linkageDeterminant first).mul (base.linkageDeterminant second)) (fun _ ↦ rfl)

/-- The generalized three-index `Dz` observable. -/
def dzObservable (base : PulseCoordinateExpansion pulse) (first second third : Fin D) :
    PulseExpansion pulse (twoLocusDzJet first second third).value :=
  PulseExpansion.ofEq
    (((base.linkageDeterminant first).mul
        ((PulseExpansion.const D pulse 1).add ((base.leftMarginal second).smul (-2)))).mul
      ((PulseExpansion.const D pulse 1).add ((base.rightMarginal third).smul (-2))))
    (fun _ ↦ rfl)

/-- The generalized four-index joint heterozygosity, a quarter of the product of one left
and one right heterozygosity. -/
def jointHeterozygosity (base : PulseCoordinateExpansion pulse)
    (first second third fourth : Fin D) :
    PulseExpansion pulse (twoLocusPi2Jet first second third fourth).value :=
  PulseExpansion.ofEq
    (((base.leftHeterozygosity first second).mul
      (base.rightHeterozygosity third fourth)).smul (1 / 4)) (fun _ ↦ rfl)

/-- Every coordinate of the closed low-order family has a second-order pulse expansion. -/
def coordinate (base : PulseCoordinateExpansion pulse) :
    ∀ feature : LowOrderLDCoordinate D,
      PulseExpansion pulse (twoLocusCoordinateJet feature).value
  | .H first second => base.leftHeterozygosity first second
  | .DD first second => base.linkageProduct first second
  | .Dz first second third => base.dzObservable first second third
  | .pi2 first second third fourth => base.jointHeterozygosity first second third fourth

end PulseCoordinateExpansion

/-! ## Velocity bridges to the corpus generator rows -/

/-- The migration velocity of cross-deme left heterozygosity is exactly the lineage
replacement stencil of the corpus's `lowOrderLDMigration` row at `H`: each lineage sitting in
the recipient deme is replaced by the source deme's lineage. -/
theorem migrationLeftHeterozygosity_velocity {D : ℕ}
    (source recipient first second : Fin D) (state : DemeHaplotypeState D) :
    ((migrationCoordinateExpansion source recipient).leftHeterozygosity first
        second).velocity state =
      (if first = recipient then
        (twoLocusHJet source second).value state -
          (twoLocusHJet first second).value state else 0) +
      (if second = recipient then
        (twoLocusHJet first source).value state -
          (twoLocusHJet first second).value state else 0) := by
  by_cases hfirst : first = recipient <;> by_cases hsecond : second = recipient <;>
    simp [PulseCoordinateExpansion.leftHeterozygosity, PulseExpansion.ofEq,
      PulseExpansion.add, PulseExpansion.mul, PulseExpansion.smul, PulseExpansion.const,
      migrationCoordinateExpansion, migrationLeftExpansion, twoLocusHJet,
      TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.mul, TwoLocusDiffusionJet.const,
      TwoLocusDiffusionJet.smul, twoLocusLeftFrequencyJet, hfirst, hsecond] <;> ring

/-- The migration velocity of cross-deme right-locus heterozygosity obeys the same
replacement stencil.  This is the row that the stored low-order generator does not carry and
that the enlarged feature family must supply. -/
theorem migrationRightHeterozygosity_velocity {D : ℕ}
    (source recipient first second : Fin D) (state : DemeHaplotypeState D) :
    ((migrationCoordinateExpansion source recipient).rightHeterozygosity first
        second).velocity state =
      (if first = recipient then
        (twoLocusRightHJet source second).value state -
          (twoLocusRightHJet first second).value state else 0) +
      (if second = recipient then
        (twoLocusRightHJet first source).value state -
          (twoLocusRightHJet first second).value state else 0) := by
  by_cases hfirst : first = recipient <;> by_cases hsecond : second = recipient <;>
    simp [PulseCoordinateExpansion.rightHeterozygosity, PulseExpansion.ofEq,
      PulseExpansion.add, PulseExpansion.mul, PulseExpansion.smul, PulseExpansion.const,
      migrationCoordinateExpansion, migrationRightExpansion, twoLocusRightHJet,
      TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.mul, TwoLocusDiffusionJet.const,
      TwoLocusDiffusionJet.smul, twoLocusRightFrequencyJet, hfirst, hsecond] <;> ring

/-- The recombination velocity of a cross-deme linkage product counts how many of its two
lineages sit in the recombining deme, matching the corpus's `lowOrderLDRecombination` row at
`DD` once the pulse fraction carries the per-lineage rate. -/
theorem recombinationLinkageProduct_velocity {D : ℕ} (target first second : Fin D)
    (state : DemeHaplotypeState D) :
    ((recombinationCoordinateExpansion target).linkageProduct first second).velocity state =
      -((if first = target then 1 else 0) + (if second = target then 1 else 0)) *
        (twoLocusDDJet first second).value state := by
  by_cases hfirst : first = target <;> by_cases hsecond : second = target <;>
    simp [PulseCoordinateExpansion.linkageProduct, PulseExpansion.ofEq, PulseExpansion.mul,
      recombinationCoordinateExpansion, recombinationLinkageExpansion,
      recombinationLinkageVelocity, twoLocusDDJet, TwoLocusDiffusionJet.mul,
      twoLocusLinkageJet, hfirst, hsecond] <;> ring

/-- The mutation velocity of cross-deme left heterozygosity is the corpus's
`twoLocusHMutationVelocity`, scaled by the number of its lineages sitting in the mutating
deme and by the two-to-one conversion between allele-flip probability and the repository's
mutation rate coordinate. -/
theorem leftMutationLeftHeterozygosity_velocity {D : ℕ} (target first second : Fin D)
    (state : DemeHaplotypeState D) :
    ((leftMutationCoordinateExpansion target).leftHeterozygosity first second).velocity
        state =
      2 * ((if first = target then 1 else 0) + (if second = target then 1 else 0)) *
        twoLocusHMutationVelocity (state first) (state second) := by
  by_cases hfirst : first = target <;> by_cases hsecond : second = target <;>
    simp [PulseCoordinateExpansion.leftHeterozygosity, PulseExpansion.ofEq,
      PulseExpansion.add, PulseExpansion.mul, PulseExpansion.smul, PulseExpansion.const,
      leftMutationCoordinateExpansion, leftMutationLeftExpansion,
      twoLocusHMutationVelocity, leftContrast, hfirst, hsecond] <;> ring

end

end Descent.Portability.PulseJetExpansion
