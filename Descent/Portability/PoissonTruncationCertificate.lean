/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SubstochasticGeneratorSemigroup

assert_below Descent.Decision Descent.Program

/-!
# Truncating the uniformized Poisson mixture leaves a certified positive suboperator

NOTE 1 equation (26) rewrites the exact semigroup of a finite killing generator as a Poisson
mixture of the powers of one defective jump kernel: with a uniformization rate dominating
every exit rate, the kernel is `1 + rate⁻¹ • Q` and the semigroup at a nonnegative duration is
the Poisson average of its powers. A computation retains finitely many of those powers. This
module proves that what it retains is a certificate of the exact object rather than an
approximation of unknown sign.

`matrixExponential_eq_poissonMixture` is equation (26) itself, derived from the corpus scalar
shift and the observation that scaling a generator and scaling a duration are the same
operation on the exponential. `poissonTruncation` retains the first finitely many terms.
`poissonTruncation_nonneg` and `poissonTruncation_le_exponential` say the retained operator is
entrywise nonnegative and entrywise below the exact semigroup, which is exactly what makes it
a positive suboperator and so an input to the sublaw certificates of
`Descent.Portability.SublawReportCertificate`. `rowSum_deficit_le` is the mass statement: the
row mass the truncation fails to account for, measured against the exact semigroup, never
exceeds the Poisson mass the truncation omitted, because every power of the jump kernel is
itself substochastic. The omitted Poisson mass is a scalar series in the rate and the
duration, computable to any precision without touching the matrix.

The substochastic theory this rests on, including that `1 + rate⁻¹ • Q` and all its powers are
substochastic, is `Descent.Portability.SubstochasticGeneratorSemigroup`; nothing of it is
restated here. What is added is the mixture identity, the truncation and its two positivity
statements, and the omitted-mass bound. The two entrywise series lemmas it needs,
`expSeries_entry_summable` and `expSeries_rowSum_term`, are taken from that module rather than
restated; `partialSum_apply` and `exponential_apply_tsum` have no equivalent there.

Several epochs. NOTE 1 observes that over several epochs the retained mass is the product of
the per-epoch retained masses. `RetainedMassCertificate` records what one truncated epoch
certifies about its exact semigroup: a positive suboperator whose rows carry at most the
retained mass and miss at most the complementary mass. `RetainedMassCertificate.mul` shows that
certificates compose with their masses multiplying, so
`poissonTruncation_epochProduct_certificate` certifies the exact multi-epoch semigroup by the
product of the per-epoch truncations, with the product of the per-epoch retained Poisson masses.
For conservative generators, as after the cemetery extension of (26),
`poissonTruncation_epochProduct_rowSum_eq` proves that the product of truncations retains
exactly that mass while the exact product carries mass one, so the certified missed mass is
attained. An exactly computed substochastic instantaneous event certifies itself with full
mass (`retainedMassCertificate_of_substochastic`) and composes by the same product step.

Scope. The choice of a truncation order is not formalized: every bound is stated for every
order and every dominating rate, and selecting them is the caller's business.

## Empirical status

None. The bodies here are algebra: a convergent matrix power series, its partial sums, and a
scalar Poisson series, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PoissonTruncationCertificate

open Descent.Coalescent SubstochasticGeneratorSemigroup

open scoped Matrix.Norms.Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Scaling the generator and scaling the duration are the same operation on the exact matrix
exponential, which is what lets a uniformization rate be moved between the two. -/
theorem matrixExponential_smul_matrix (A : Matrix ι ι ℝ) (scale time : ℝ) :
    matrixExponential (scale • A) time = matrixExponential A (time * scale) := by
  unfold matrixExponential
  simp only [smul_smul]

/-- **NOTE 1 equation (26).** The defective jump kernel a killing generator induces when time
is run at a dominating uniformization rate. -/
noncomputable def uniformization (Q : Matrix ι ι ℝ) (uniformRate : ℝ) : Matrix ι ι ℝ :=
  (1 : Matrix ι ι ℝ) + uniformRate⁻¹ • Q

/-- **NOTE 1 equation (26).** The exact semigroup of a killing generator is the Poisson
mixture of the powers of its uniformization kernel, at Poisson parameter the rate times the
duration. -/
theorem matrixExponential_eq_poissonMixture (Q : Matrix ι ι ℝ) (uniformRate : ℝ)
    (hpos : 0 < uniformRate) (time : ℝ) :
    matrixExponential Q time =
      Real.exp (-(uniformRate * time)) •
        matrixExponential (uniformization Q uniformRate) (uniformRate * time) := by
  have hshape : uniformization Q uniformRate =
      uniformRate⁻¹ • Q + (1 : ℝ) • (1 : Matrix ι ι ℝ) := by
    unfold uniformization
    rw [one_smul, add_comm]
  have hone : uniformRate * time * (1 : ℝ) = uniformRate * time := mul_one _
  have hcancel : uniformRate * time * uniformRate⁻¹ = time := by
    rw [mul_comm uniformRate time, mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), mul_one]
  have hzero : -(uniformRate * time) + uniformRate * time = 0 := by ring
  rw [hshape, matrixExponential_scalar_shift, matrixExponential_smul_matrix, hone, hcancel,
    smul_smul, ← Real.exp_add, hzero, Real.exp_zero, one_smul]

/-- **NOTE 1 equation (26), truncated.** The retained terms of the uniformized Poisson
mixture. -/
noncomputable def poissonTruncation (Q : Matrix ι ι ℝ) (uniformRate time : ℝ) (terms : ℕ) :
    Matrix ι ι ℝ :=
  Real.exp (-(uniformRate * time)) •
    matrixExponentialPartialSum (uniformization Q uniformRate) (uniformRate * time) terms

/-- The Poisson mass a truncation retains: a scalar series in the rate and the duration that
mentions no matrix at all. -/
noncomputable def retainedPoissonMass (uniformRate time : ℝ) (terms : ℕ) : ℝ :=
  Real.exp (-(uniformRate * time)) *
    ∑ power ∈ Finset.range terms, ((power.factorial : ℝ)⁻¹) * (uniformRate * time) ^ power

/-- Entries of a finite Taylor evaluation are the partial sums of the entrywise series. -/
theorem partialSum_apply (A : Matrix ι ι ℝ) (time : ℝ) (terms : ℕ) (row column : ι) :
    matrixExponentialPartialSum A time terms row column =
      ∑ power ∈ Finset.range terms,
        (((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)) row column := by
  unfold matrixExponentialPartialSum
  rw [Matrix.sum_apply]

/-- Each entry of the exact matrix exponential is the sum of the entrywise series. -/
theorem exponential_apply_tsum (A : Matrix ι ι ℝ) (time : ℝ) (row column : ι) :
    matrixExponential A time row column =
      ∑' power : ℕ, (((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)) row column := by
  have hmatrix : Summable (fun power : ℕ ↦
      ((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)) :=
    NormedSpace.expSeries_summable' (time • A)
  unfold matrixExponential
  rw [tsum_apply hmatrix, tsum_apply (Pi.summable.mp hmatrix row)]

/-- The scaled uniformization kernel is entrywise nonnegative at a nonnegative duration. -/
theorem scaled_uniformization_nonneg (Q : Matrix ι ι ℝ) (hQ : KillingGenerator Q)
    (uniformRate : ℝ) (hpos : 0 < uniformRate) (hdominates : ∀ row, -Q row row ≤ uniformRate)
    (time : ℝ) (htime : 0 ≤ time) (row column : ι) :
    0 ≤ ((uniformRate * time) • uniformization Q uniformRate) row column := by
  have hsub : SubstochasticMatrix (uniformization Q uniformRate) :=
    substochastic_uniformization Q hQ uniformRate hpos hdominates
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (mul_nonneg hpos.le htime) (hsub.entry_nonneg row column)

/-- The retained operator of a truncation is entrywise nonnegative. -/
theorem poissonTruncation_nonneg (Q : Matrix ι ι ℝ) (hQ : KillingGenerator Q)
    (uniformRate : ℝ) (hpos : 0 < uniformRate) (hdominates : ∀ row, -Q row row ≤ uniformRate)
    (time : ℝ) (htime : 0 ≤ time) (terms : ℕ) (row column : ι) :
    0 ≤ poissonTruncation Q uniformRate time terms row column := by
  have hscaled := scaled_uniformization_nonneg Q hQ uniformRate hpos hdominates time htime
  unfold poissonTruncation
  simp only [Matrix.smul_apply, smul_eq_mul]
  refine mul_nonneg (Real.exp_pos _).le ?_
  rw [partialSum_apply]
  refine Finset.sum_nonneg fun power _ ↦ ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (matrix_pow_apply_nonneg_of_nonneg _ hscaled power row column)

/-- **NOTE 1 equation (26), positivity of the truncation.** The retained operator sits
entrywise below the exact semigroup, so it is a positive suboperator of it and every bounded
report it certifies is certified against the exact object. -/
theorem poissonTruncation_le_exponential (Q : Matrix ι ι ℝ) (hQ : KillingGenerator Q)
    (uniformRate : ℝ) (hpos : 0 < uniformRate) (hdominates : ∀ row, -Q row row ≤ uniformRate)
    (time : ℝ) (htime : 0 ≤ time) (terms : ℕ) (row column : ι) :
    poissonTruncation Q uniformRate time terms row column ≤
      matrixExponential Q time row column := by
  have hscaled := scaled_uniformization_nonneg Q hQ uniformRate hpos hdominates time htime
  have htermNonneg : ∀ power : ℕ,
      0 ≤ (((power.factorial : ℝ)⁻¹) •
        (((uniformRate * time) • uniformization Q uniformRate) ^ power)) row column := by
    intro power
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (matrix_pow_apply_nonneg_of_nonneg _ hscaled power row column)
  have hpartial : matrixExponentialPartialSum (uniformization Q uniformRate)
        (uniformRate * time) terms row column ≤
      matrixExponential (uniformization Q uniformRate) (uniformRate * time) row column := by
    rw [partialSum_apply, exponential_apply_tsum]
    exact (expSeries_entry_summable _ _ row column).sum_le_tsum (Finset.range terms)
      fun power _ ↦ htermNonneg power
  rw [matrixExponential_eq_poissonMixture Q uniformRate hpos time]
  unfold poissonTruncation
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left hpartial (Real.exp_pos _).le

/-- The row mass of a product is the first operator's row weighted by the second operator's
row masses. -/
theorem rowMass_mul (P R : Matrix ι ι ℝ) (row : ι) :
    ∑ column, (P * R) row column = ∑ middle, P row middle * ∑ column, R middle column := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Two operators whose rows each carry a constant mass compose to an operator whose rows carry
the product of the two masses. -/
theorem rowMass_mul_of_constant {P R : Matrix ι ι ℝ} {first second : ℝ}
    (hP : ∀ row, ∑ column, P row column = first)
    (hR : ∀ row, ∑ column, R row column = second) (row : ι) :
    ∑ column, (P * R) row column = first * second := by
  rw [rowMass_mul]
  simp only [hR]
  rw [← Finset.sum_mul, hP]

/-- The row mass a truncation retains is the Poisson-weighted row mass of the retained powers of
the uniformization kernel. -/
theorem poissonTruncation_rowSum_eq_series (Q : Matrix ι ι ℝ) (uniformRate time : ℝ)
    (terms : ℕ) (row : ι) :
    ∑ column, poissonTruncation Q uniformRate time terms row column
      = Real.exp (-(uniformRate * time)) * ∑ power ∈ Finset.range terms,
        ((power.factorial : ℝ)⁻¹) * ((uniformRate * time) ^ power *
          ∑ column, (uniformization Q uniformRate ^ power) row column) := by
  unfold poissonTruncation
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1
  simp only [partialSum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun power _ ↦
    expSeries_rowSum_term (uniformization Q uniformRate) (uniformRate * time) row power

/-- **NOTE 1 equation (26), omitted mass.** The row mass the truncation fails to account for,
measured against the exact semigroup, never exceeds the Poisson mass it omitted. Every power
of the uniformization kernel is substochastic, so each discarded term contributes at most its
own Poisson weight. -/
theorem rowSum_deficit_le (Q : Matrix ι ι ℝ) (hQ : KillingGenerator Q) (uniformRate : ℝ)
    (hpos : 0 < uniformRate) (hdominates : ∀ row, -Q row row ≤ uniformRate) (time : ℝ)
    (htime : 0 ≤ time) (terms : ℕ) (row : ι) :
    (∑ column, matrixExponential Q time row column) -
        ∑ column, poissonTruncation Q uniformRate time terms row column ≤
      1 - retainedPoissonMass uniformRate time terms := by
  have hsub : SubstochasticMatrix (uniformization Q uniformRate) :=
    substochastic_uniformization Q hQ uniformRate hpos hdominates
  have hrateNonneg : 0 ≤ uniformRate * time := mul_nonneg hpos.le htime
  have hexpPos : 0 < Real.exp (-(uniformRate * time)) := Real.exp_pos _
  have hexpCancel : Real.exp (-(uniformRate * time)) * Real.exp (uniformRate * time) = 1 := by
    rw [← Real.exp_add]
    simp
  have hfullRow : ∑ column, matrixExponential Q time row column
      = Real.exp (-(uniformRate * time)) * ∑' power : ℕ, ((power.factorial : ℝ)⁻¹) *
        ((uniformRate * time) ^ power *
          ∑ column, (uniformization Q uniformRate ^ power) row column) := by
    rw [matrixExponential_eq_poissonMixture Q uniformRate hpos time]
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, exponential_rowSum_eq_tsum]
  have htruncRow := poissonTruncation_rowSum_eq_series Q uniformRate time terms row
  have hsummable := exponential_rowSum_summable (uniformization Q uniformRate)
    (uniformRate * time) row
  have hmajorant : Summable (fun power : ℕ ↦
      ((power.factorial : ℝ)⁻¹) * (uniformRate * time) ^ power) := by
    simpa [smul_eq_mul] using NormedSpace.expSeries_summable' (𝕂 := ℝ) (uniformRate * time)
  have hcompare : ∀ power : ℕ,
      (((power + terms).factorial : ℝ)⁻¹) * ((uniformRate * time) ^ (power + terms) *
          ∑ column, (uniformization Q uniformRate ^ (power + terms)) row column) ≤
        (((power + terms).factorial : ℝ)⁻¹) * (uniformRate * time) ^ (power + terms) := by
    intro power
    have hfactorial : (0 : ℝ) ≤ (((power + terms).factorial : ℝ)⁻¹) :=
      inv_nonneg.mpr (Nat.cast_nonneg _)
    have hpow : (0 : ℝ) ≤ (uniformRate * time) ^ (power + terms) :=
      pow_nonneg hrateNonneg _
    have hrow : ∑ column, (uniformization Q uniformRate ^ (power + terms)) row column ≤ 1 :=
      (substochastic_pow hsub (power + terms)).rowSum_le_one row
    have hinner : (uniformRate * time) ^ (power + terms) *
        ∑ column, (uniformization Q uniformRate ^ (power + terms)) row column ≤
          (uniformRate * time) ^ (power + terms) := by
      calc (uniformRate * time) ^ (power + terms) *
            ∑ column, (uniformization Q uniformRate ^ (power + terms)) row column
          ≤ (uniformRate * time) ^ (power + terms) * 1 :=
            mul_le_mul_of_nonneg_left hrow hpow
        _ = (uniformRate * time) ^ (power + terms) := mul_one _
    exact mul_le_mul_of_nonneg_left hinner hfactorial
  have htail := ((summable_nat_add_iff terms).mpr hsummable).tsum_le_tsum hcompare
    ((summable_nat_add_iff terms).mpr hmajorant)
  have hsplit := hsummable.sum_add_tsum_nat_add terms
  have hmajorantSplit := hmajorant.sum_add_tsum_nat_add terms
  rw [tsum_factorial_pow (uniformRate * time)] at hmajorantSplit
  have hsplitScaled := congrArg (fun value ↦ Real.exp (-(uniformRate * time)) * value) hsplit
  have hmajorantScaled :=
    congrArg (fun value ↦ Real.exp (-(uniformRate * time)) * value) hmajorantSplit
  simp only [mul_add] at hsplitScaled hmajorantScaled
  have htailScaled := mul_le_mul_of_nonneg_left htail hexpPos.le
  unfold retainedPoissonMass
  rw [hfullRow, htruncRow]
  linarith [hsplitScaled, hmajorantScaled, htailScaled, hexpCancel]

/-- The retained Poisson mass is nonnegative at a nonnegative Poisson parameter. -/
theorem retainedPoissonMass_nonneg (uniformRate time : ℝ) (hrate : 0 ≤ uniformRate * time)
    (terms : ℕ) : 0 ≤ retainedPoissonMass uniformRate time terms := by
  unfold retainedPoissonMass
  refine mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun power _ ↦ ?_)
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_nonneg hrate power)

/-- The retained Poisson mass never exceeds one: the retained weights are part of the Poisson
law. -/
theorem retainedPoissonMass_le_one (uniformRate time : ℝ) (hrate : 0 ≤ uniformRate * time)
    (terms : ℕ) : retainedPoissonMass uniformRate time terms ≤ 1 := by
  have hmajorant : Summable (fun power : ℕ ↦
      ((power.factorial : ℝ)⁻¹) * (uniformRate * time) ^ power) := by
    simpa [smul_eq_mul] using NormedSpace.expSeries_summable' (𝕂 := ℝ) (uniformRate * time)
  have hpartial : ∑ power ∈ Finset.range terms,
      ((power.factorial : ℝ)⁻¹) * (uniformRate * time) ^ power
        ≤ Real.exp (uniformRate * time) := by
    rw [← tsum_factorial_pow (uniformRate * time)]
    exact hmajorant.sum_le_tsum (Finset.range terms) fun power _ ↦
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_nonneg hrate power)
  have hcancel : Real.exp (-(uniformRate * time)) * Real.exp (uniformRate * time) = 1 := by
    rw [← Real.exp_add]
    simp
  unfold retainedPoissonMass
  calc Real.exp (-(uniformRate * time)) * ∑ power ∈ Finset.range terms,
        ((power.factorial : ℝ)⁻¹) * (uniformRate * time) ^ power
      ≤ Real.exp (-(uniformRate * time)) * Real.exp (uniformRate * time) :=
        mul_le_mul_of_nonneg_left hpartial (Real.exp_pos _).le
    _ = 1 := hcancel

/-- The rows of a truncation carry at most the retained Poisson mass, because every retained
power of the uniformization kernel is substochastic. -/
theorem poissonTruncation_rowSum_le_retained (Q : Matrix ι ι ℝ) (hQ : KillingGenerator Q)
    (uniformRate : ℝ) (hpos : 0 < uniformRate) (hdominates : ∀ row, -Q row row ≤ uniformRate)
    (time : ℝ) (htime : 0 ≤ time) (terms : ℕ) (row : ι) :
    ∑ column, poissonTruncation Q uniformRate time terms row column
      ≤ retainedPoissonMass uniformRate time terms := by
  have hsub : SubstochasticMatrix (uniformization Q uniformRate) :=
    substochastic_uniformization Q hQ uniformRate hpos hdominates
  have hrateNonneg : 0 ≤ uniformRate * time := mul_nonneg hpos.le htime
  rw [poissonTruncation_rowSum_eq_series]
  unfold retainedPoissonMass
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun power _ ↦ ?_) (Real.exp_pos _).le
  have hrow : ∑ column, (uniformization Q uniformRate ^ power) row column ≤ 1 :=
    (substochastic_pow hsub power).rowSum_le_one row
  exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (pow_nonneg hrateNonneg power) hrow)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- A retained-mass certificate for an exact substochastic operator: a positive suboperator whose
rows carry at most the certified mass, and whose rows fall short of the exact operator's by at
most the complementary mass.  These are the two inputs the sublaw bounds (24) and (25) need. -/
structure RetainedMassCertificate (retained exact : Matrix ι ι ℝ) (mass : ℝ) : Prop where
  /-- The retained operator is positive. -/
  retained_nonneg : ∀ row column, 0 ≤ retained row column
  /-- The retained operator sits entrywise below the exact one. -/
  retained_le_exact : ∀ row column, retained row column ≤ exact row column
  /-- The exact operator creates no mass. -/
  exact_rowSum_le_one : ∀ row, ∑ column, exact row column ≤ 1
  /-- The certified mass is nonnegative. -/
  mass_nonneg : 0 ≤ mass
  /-- The certified mass is at most one. -/
  mass_le_one : mass ≤ 1
  /-- The retained rows carry at most the certified mass. -/
  retained_rowSum_le : ∀ row, ∑ column, retained row column ≤ mass
  /-- The mass the retained operator misses is at most the complementary mass. -/
  deficit_le : ∀ row, ∑ column, exact row column - ∑ column, retained row column ≤ 1 - mass

/-- An exactly computed substochastic step certifies itself with full mass; this is how an
instantaneous event between epochs enters a certified history. -/
theorem retainedMassCertificate_of_substochastic {step : Matrix ι ι ℝ}
    (hstep : SubstochasticMatrix step) : RetainedMassCertificate step step 1 where
  retained_nonneg := hstep.entry_nonneg
  retained_le_exact := fun _ _ ↦ le_rfl
  exact_rowSum_le_one := hstep.rowSum_le_one
  mass_nonneg := zero_le_one
  mass_le_one := le_rfl
  retained_rowSum_le := hstep.rowSum_le_one
  deficit_le := fun _ ↦ by simp

/-- The identity certifies itself with full mass, so the certificate class is inhabited on every
finite state space. -/
theorem retainedMassCertificate_one :
    RetainedMassCertificate (1 : Matrix ι ι ℝ) 1 1 :=
  retainedMassCertificate_of_substochastic substochastic_one

/-- **Certificates compose.**  Running two certified steps in sequence certifies the composed
step with the product of the two masses: the missed mass of the composition is at most the
first step's missed mass plus the retained part of the first step times the second step's
missed mass. -/
theorem RetainedMassCertificate.mul {retainedFirst exactFirst retainedSecond exactSecond :
      Matrix ι ι ℝ} {massFirst massSecond : ℝ}
    (hfirst : RetainedMassCertificate retainedFirst exactFirst massFirst)
    (hsecond : RetainedMassCertificate retainedSecond exactSecond massSecond) :
    RetainedMassCertificate (retainedFirst * retainedSecond) (exactFirst * exactSecond)
      (massFirst * massSecond) := by
  have hexactNonneg : ∀ row column, 0 ≤ exactFirst row column := fun row column ↦
    (hfirst.retained_nonneg row column).trans (hfirst.retained_le_exact row column)
  refine ⟨?_, ?_, ?_, mul_nonneg hfirst.mass_nonneg hsecond.mass_nonneg, ?_, ?_, ?_⟩
  · intro row column
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg fun middle _ ↦
      mul_nonneg (hfirst.retained_nonneg row middle) (hsecond.retained_nonneg middle column)
  · intro row column
    rw [Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_le_sum fun middle _ ↦
      (mul_le_mul_of_nonneg_right (hfirst.retained_le_exact row middle)
        (hsecond.retained_nonneg middle column)).trans
        (mul_le_mul_of_nonneg_left (hsecond.retained_le_exact middle column)
          (hexactNonneg row middle))
  · intro row
    rw [rowMass_mul]
    calc ∑ middle, exactFirst row middle * ∑ column, exactSecond middle column
        ≤ ∑ middle, exactFirst row middle :=
          Finset.sum_le_sum fun middle _ ↦ mul_le_of_le_one_right (hexactNonneg row middle)
            (hsecond.exact_rowSum_le_one middle)
      _ ≤ 1 := hfirst.exact_rowSum_le_one row
  · calc massFirst * massSecond ≤ 1 * massSecond :=
        mul_le_mul_of_nonneg_right hfirst.mass_le_one hsecond.mass_nonneg
      _ = massSecond := one_mul massSecond
      _ ≤ 1 := hsecond.mass_le_one
  · intro row
    rw [rowMass_mul]
    calc ∑ middle, retainedFirst row middle * ∑ column, retainedSecond middle column
        ≤ ∑ middle, retainedFirst row middle * massSecond :=
          Finset.sum_le_sum fun middle _ ↦ mul_le_mul_of_nonneg_left
            (hsecond.retained_rowSum_le middle) (hfirst.retained_nonneg row middle)
      _ = (∑ middle, retainedFirst row middle) * massSecond := by rw [Finset.sum_mul]
      _ ≤ massFirst * massSecond :=
          mul_le_mul_of_nonneg_right (hfirst.retained_rowSum_le row) hsecond.mass_nonneg
  · intro row
    rw [rowMass_mul, rowMass_mul]
    have hsplit : ∑ middle, exactFirst row middle * ∑ column, exactSecond middle column
          - ∑ middle, retainedFirst row middle * ∑ column, retainedSecond middle column
        = ∑ middle, (exactFirst row middle - retainedFirst row middle) *
            ∑ column, exactSecond middle column
          + ∑ middle, retainedFirst row middle *
            (∑ column, exactSecond middle column - ∑ column, retainedSecond middle column) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun middle _ ↦ by ring
    have hmissedFirst : ∑ middle, (exactFirst row middle - retainedFirst row middle) *
          ∑ column, exactSecond middle column
        ≤ ∑ column, exactFirst row column - ∑ column, retainedFirst row column := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum fun middle _ ↦
        mul_le_of_le_one_right (sub_nonneg.mpr (hfirst.retained_le_exact row middle))
          (hsecond.exact_rowSum_le_one middle)
    have hmissedSecond : ∑ middle, retainedFirst row middle *
          (∑ column, exactSecond middle column - ∑ column, retainedSecond middle column)
        ≤ (∑ middle, retainedFirst row middle) * (1 - massSecond) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun middle _ ↦
        mul_le_mul_of_nonneg_left (hsecond.deficit_le middle) (hfirst.retained_nonneg row middle)
    have hretained : (∑ middle, retainedFirst row middle) * (1 - massSecond)
        ≤ massFirst * (1 - massSecond) :=
      mul_le_mul_of_nonneg_right (hfirst.retained_rowSum_le row)
        (sub_nonneg.mpr hsecond.mass_le_one)
    rw [hsplit]
    linarith [hmissedFirst, hmissedSecond, hretained, hfirst.deficit_le row]

/-- **NOTE 1 equation (26) as a certificate.**  One truncated epoch certifies the exact semigroup
of its killing generator with the retained Poisson mass. -/
theorem poissonTruncation_certificate (Q : Matrix ι ι ℝ) (hQ : KillingGenerator Q)
    (uniformRate : ℝ) (hpos : 0 < uniformRate) (hdominates : ∀ row, -Q row row ≤ uniformRate)
    (time : ℝ) (htime : 0 ≤ time) (terms : ℕ) :
    RetainedMassCertificate (poissonTruncation Q uniformRate time terms)
      (matrixExponential Q time) (retainedPoissonMass uniformRate time terms) where
  retained_nonneg :=
    poissonTruncation_nonneg Q hQ uniformRate hpos hdominates time htime terms
  retained_le_exact :=
    poissonTruncation_le_exponential Q hQ uniformRate hpos hdominates time htime terms
  exact_rowSum_le_one := (matrixExponential_substochastic Q hQ time htime).rowSum_le_one
  mass_nonneg := retainedPoissonMass_nonneg uniformRate time (mul_nonneg hpos.le htime) terms
  mass_le_one := retainedPoissonMass_le_one uniformRate time (mul_nonneg hpos.le htime) terms
  retained_rowSum_le :=
    poissonTruncation_rowSum_le_retained Q hQ uniformRate hpos hdominates time htime terms
  deficit_le := rowSum_deficit_le Q hQ uniformRate hpos hdominates time htime terms

/-- **NOTE 1 equation (26), several epochs.**  A chronological history of epochs, each with its
own killing generator, dominating uniformization rate, nonnegative duration and truncation
order, gives a product of truncations that is a positive suboperator of the exact multi-epoch
semigroup; its rows carry at most the product of the per-epoch retained Poisson masses and miss
at most one minus that product. -/
theorem poissonTruncation_epochProduct_certificate
    (epochs : List (Matrix ι ι ℝ × ℝ × ℝ × ℕ))
    (hepochs : ∀ epoch ∈ epochs, KillingGenerator epoch.1 ∧ 0 < epoch.2.1 ∧
      (∀ row, -epoch.1 row row ≤ epoch.2.1) ∧ 0 ≤ epoch.2.2.1) :
    RetainedMassCertificate
      (epochs.map fun epoch ↦
        poissonTruncation epoch.1 epoch.2.1 epoch.2.2.1 epoch.2.2.2).prod
      (epochs.map fun epoch ↦ matrixExponential epoch.1 epoch.2.2.1).prod
      (epochs.map fun epoch ↦ retainedPoissonMass epoch.2.1 epoch.2.2.1 epoch.2.2.2).prod := by
  induction epochs with
  | nil => simpa using retainedMassCertificate_one
  | cons epoch rest ih =>
    simp only [List.map_cons, List.prod_cons]
    obtain ⟨hgenerator, hpos, hdominates, htime⟩ := hepochs epoch (by simp)
    exact (poissonTruncation_certificate epoch.1 hgenerator epoch.2.1 hpos hdominates
      epoch.2.2.1 htime epoch.2.2.2).mul (ih fun other hother ↦ hepochs other (by simp [hother]))

/-- For a conservative generator every power of the uniformization kernel carries row mass one,
so the rows of a truncation carry exactly the retained Poisson mass. -/
theorem poissonTruncation_rowSum_eq_retained (Q : Matrix ι ι ℝ)
    (hzero : ∀ row, ∑ column, Q row column = 0) (uniformRate time : ℝ) (terms : ℕ) (row : ι) :
    ∑ column, poissonTruncation Q uniformRate time terms row column
      = retainedPoissonMass uniformRate time terms := by
  have hkernel : ∀ source, ∑ column, uniformization Q uniformRate source column = 1 := by
    intro source
    have hsplit : ∑ column, uniformization Q uniformRate source column
        = (∑ column, (1 : Matrix ι ι ℝ) source column)
          + uniformRate⁻¹ * ∑ column, Q source column := by
      simp [uniformization, Matrix.add_apply, Finset.sum_add_distrib, Finset.mul_sum]
    rw [hsplit, hzero source, mul_zero, add_zero]
    simp [Matrix.one_apply]
  have hpow : ∀ power : ℕ, ∀ source,
      ∑ column, (uniformization Q uniformRate ^ power) source column = 1 := by
    intro power
    induction power with
    | zero => intro source; simp [Matrix.one_apply]
    | succ k ih =>
      intro source
      rw [pow_succ, rowMass_mul_of_constant ih hkernel source, one_mul]
  rw [poissonTruncation_rowSum_eq_series]
  unfold retainedPoissonMass
  congr 1
  exact Finset.sum_congr rfl fun power _ ↦ by rw [hpow power row, mul_one]

/-- **NOTE 1 equation (26), several epochs, conservative case.**  When every epoch's generator
is conservative, as it is after the cemetery extension, the exact multi-epoch semigroup carries
row mass exactly one and the product of truncations carries exactly the product of the
per-epoch retained Poisson masses, so the certified missed mass is attained. -/
theorem poissonTruncation_epochProduct_rowSum_eq
    (epochs : List (Matrix ι ι ℝ × ℝ × ℝ × ℕ))
    (hzero : ∀ epoch ∈ epochs, ∀ row, ∑ column, epoch.1 row column = 0) :
    (∀ row, ∑ column, (epochs.map fun epoch ↦
        poissonTruncation epoch.1 epoch.2.1 epoch.2.2.1 epoch.2.2.2).prod row column
      = (epochs.map fun epoch ↦ retainedPoissonMass epoch.2.1 epoch.2.2.1 epoch.2.2.2).prod) ∧
    (∀ row, ∑ column,
      (epochs.map fun epoch ↦ matrixExponential epoch.1 epoch.2.2.1).prod row column = 1) := by
  induction epochs with
  | nil => simp [Matrix.one_apply]
  | cons epoch rest ih =>
    simp only [List.map_cons, List.prod_cons]
    have hhead := hzero epoch (by simp)
    obtain ⟨hrestTruncation, hrestExact⟩ := ih fun other hother ↦ hzero other (by simp [hother])
    refine ⟨fun row ↦ ?_, fun row ↦ ?_⟩
    · exact rowMass_mul_of_constant
        (fun source ↦ poissonTruncation_rowSum_eq_retained epoch.1 hhead epoch.2.1 epoch.2.2.1
          epoch.2.2.2 source)
        hrestTruncation row
    · rw [rowMass_mul_of_constant
        (fun source ↦ exponential_rowSum_eq_one epoch.1 hhead epoch.2.2.1 source)
        hrestExact row, one_mul]

end Descent.Portability.PoissonTruncationCertificate
