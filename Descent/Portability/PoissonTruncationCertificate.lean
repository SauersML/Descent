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
statements, and the omitted-mass bound.

Scope: one epoch. NOTE 1 observes that over several epochs the retained mass is the product of
the per-epoch retained masses; that product statement is not formalized here. Nor is the
choice of a truncation order: the bound is stated for every order and every dominating rate,
and selecting them is the caller's business.

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

/-- The entrywise exponential series converges. -/
theorem expSeries_entry_summable (A : Matrix ι ι ℝ) (time : ℝ) (row column : ι) :
    Summable (fun power : ℕ ↦
      (((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)) row column) := by
  have hmatrix : Summable (fun power : ℕ ↦
      ((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)) :=
    NormedSpace.expSeries_summable' (time • A)
  exact Pi.summable.mp (Pi.summable.mp hmatrix row) column

/-- Each entry of the exact matrix exponential is the sum of the entrywise series. -/
theorem exponential_apply_tsum (A : Matrix ι ι ℝ) (time : ℝ) (row column : ι) :
    matrixExponential A time row column =
      ∑' power : ℕ, (((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)) row column := by
  have hmatrix : Summable (fun power : ℕ ↦
      ((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)) :=
    NormedSpace.expSeries_summable' (time • A)
  unfold matrixExponential
  rw [tsum_apply hmatrix, tsum_apply (Pi.summable.mp hmatrix row)]

/-- The row mass of one term of the entrywise exponential series. -/
theorem rowSum_expSeries_term (A : Matrix ι ι ℝ) (time : ℝ) (row : ι) (power : ℕ) :
    ∑ column, (((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)) row column
      = ((power.factorial : ℝ)⁻¹) * (time ^ power * ∑ column, (A ^ power) row column) := by
  rw [smul_pow]
  simp [Finset.mul_sum]

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
  have htruncRow : ∑ column, poissonTruncation Q uniformRate time terms row column
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
      rowSum_expSeries_term (uniformization Q uniformRate) (uniformRate * time) row power
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

end Descent.Portability.PoissonTruncationCertificate
