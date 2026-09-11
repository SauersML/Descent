/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.StructuredPresentDay

assert_below Descent.Decision Descent.Program

/-!
# Substochastic semigroups of finite killing generators

NOTE1 §4.2 evaluates a finite ancestral likelihood as `v(t) = e^{tQ} v(0)` for a generator `Q`
whose off-diagonal entries are nonnegative jump rates and whose rows sum to at most zero,
the deficit being the rate of absorption into the cemetery.  This module proves that the exact
matrix exponential of such a generator is a substochastic operator: entries are nonnegative
and every row sums to at most one.  Entrywise nonnegativity is the corpus theorem
`Descent.Coalescent.matrixExponential_apply_nonneg_of_metzler`; what is added here is the
mass bound, the conservative case, and the closure properties that a multi-epoch history
needs.

The route is the diagonal shift already used in the corpus.  For an arbitrary real scalar `c`
the exponential of `A + c • 1` is `Real.exp (t * c)` times the exponential of `A`; this is
proved once, from the commuting-summand addition formula, and is the only analytic input.
Choosing `c` to be the corpus shift `matrixMetzlerShift Q` makes `Q + c • 1` entrywise
nonnegative with rows summing to at most `c`, whence every power has row sums at most `c ^ k`
and the exponential has row sums at most `Real.exp (t * c)`.  Cancelling the two exponentials
gives row sums at most one for `e^{tQ}` itself.

Substochastic matrices are closed under products, powers and finite list products, so a
chronological list of epochs, each an exponential of its own killing generator run for its own
nonnegative duration, composes to a substochastic operator.  When every row of `Q` sums to
exactly zero the same series computation gives row sums exactly one, so no mass is lost: this
is the conservative case, recorded both as a row-sum identity and as the statement that
the constant vector is a fixed point.  The uniformization
operator `1 + λ⁻¹ • Q` of (26) is substochastic whenever `λ` dominates every exit rate, and
so is each of its powers `P ^ k`; those are the positive suboperators whose Poisson weights
the retained-mass certificate multiplies.

Scope.  This module supplies positivity and mass control only.  The omitted mass of a
truncated Poisson mixture is bounded in `Descent.Portability.SublawReportCertificate`, which
owns equations (24) and (25); nothing here duplicates it, and the Poisson weights themselves
are not summed here.  The generator identity (19) of NOTE1 §4.2, which derives the rates
`q_{ξη}` from coalescent duality with recombination, is not formalized anywhere in the corpus.

## Empirical status

None.  The bodies here are algebra: a matrix exponential is a convergent power series in a
supplied rate table, so no measurement can bear on the statements.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SubstochasticGeneratorSemigroup

open Descent.Coalescent

open scoped Matrix.Norms.Operator

variable {ι : Type*} [Fintype ι]

/-- A finite substochastic matrix: nonnegative entries and rows summing to at most one.
These are exactly the transfer operators of a defective finite Markov step. -/
structure SubstochasticMatrix (P : Matrix ι ι ℝ) : Prop where
  /-- No entry is negative. -/
  entry_nonneg : ∀ row column, 0 ≤ P row column
  /-- No row creates mass. -/
  rowSum_le_one : ∀ row, ∑ column, P row column ≤ 1

/-- A finite killing generator: off-diagonal rates are nonnegative, so the matrix is Metzler,
and every row sums to at most zero, so mass may be absorbed but never created. -/
structure KillingGenerator (Q : Matrix ι ι ℝ) : Prop where
  /-- Off-diagonal entries are jump rates. -/
  metzler : Matrix.IsMetzler Q
  /-- The row deficit is the absorption rate. -/
  rowSum_nonpos : ∀ row, ∑ column, Q row column ≤ 0

/-- Composing two defective steps is a defective step. -/
theorem substochastic_mul {P R : Matrix ι ι ℝ} (hP : SubstochasticMatrix P)
    (hR : SubstochasticMatrix R) : SubstochasticMatrix (P * R) where
  entry_nonneg := by
    intro row column
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg fun middle _ ↦
      mul_nonneg (hP.entry_nonneg row middle) (hR.entry_nonneg middle column)
  rowSum_le_one := by
    intro row
    have hswap : ∑ column, (P * R) row column
        = ∑ middle, P row middle * ∑ column, R middle column := by
      simp only [Matrix.mul_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hswap]
    calc ∑ middle, P row middle * ∑ column, R middle column
        ≤ ∑ middle, P row middle * 1 :=
          Finset.sum_le_sum fun middle _ ↦
            mul_le_mul_of_nonneg_left (hR.rowSum_le_one middle) (hP.entry_nonneg row middle)
      _ = ∑ middle, P row middle := by simp
      _ ≤ 1 := hP.rowSum_le_one row

/-- The identity is substochastic, so the class is inhabited on every finite state space. -/
theorem substochastic_one [DecidableEq ι] : SubstochasticMatrix (1 : Matrix ι ι ℝ) where
  entry_nonneg := by
    intro row column
    by_cases h : row = column <;> simp [Matrix.one_apply, h]
  rowSum_le_one := by
    intro row
    simp [Matrix.one_apply]

/-- Every power of a defective step is a defective step; these are the positive suboperators
`P ^ k` of the uniformization formula (26). -/
theorem substochastic_pow [DecidableEq ι] {P : Matrix ι ι ℝ} (hP : SubstochasticMatrix P)
    (power : ℕ) : SubstochasticMatrix (P ^ power) := by
  induction power with
  | zero => simpa using substochastic_one
  | succ k ih =>
    rw [pow_succ]
    exact substochastic_mul ih hP

/-- A chronological list of defective steps composes to a defective step. -/
theorem substochastic_listProd [DecidableEq ι] (operators : List (Matrix ι ι ℝ))
    (hoperators : ∀ P ∈ operators, SubstochasticMatrix P) :
    SubstochasticMatrix operators.prod := by
  induction operators with
  | nil => simpa using substochastic_one
  | cons P rest ih =>
    rw [List.prod_cons]
    exact substochastic_mul (hoperators P (by simp)) (ih fun R hR ↦ hoperators R (by simp [hR]))

section Witnesses

/-- The generator of a finite jump process with a supplied nonnegative rate table: the exit
rate sits on the diagonal.  Its rows sum to zero, so it is a conservative generator. -/
def jumpGenerator [DecidableEq ι] (rate : ι → ι → ℝ) : Matrix ι ι ℝ :=
  fun row column ↦
    if row = column then -∑ target ∈ Finset.univ.erase row, rate row target
    else rate row column

/-- Every nonnegative rate table yields a killing generator, so the class is inhabited by a
nontrivial operator on every finite state space. -/
theorem killingGenerator_jumpGenerator [DecidableEq ι] (rate : ι → ι → ℝ)
    (hrate : ∀ row column, 0 ≤ rate row column) :
    KillingGenerator (jumpGenerator rate) where
  metzler := by
    intro row column hne
    have hentry : jumpGenerator rate row column = rate row column := by
      simp [jumpGenerator, hne]
    rw [hentry]
    exact hrate row column
  rowSum_nonpos := by
    intro row
    have hsplit : jumpGenerator rate row row
        + ∑ column ∈ Finset.univ.erase row, jumpGenerator rate row column
        = ∑ column, jumpGenerator rate row column :=
      Finset.add_sum_erase _ _ (Finset.mem_univ row)
    have hdiag : jumpGenerator rate row row
        = -∑ target ∈ Finset.univ.erase row, rate row target := by
      simp [jumpGenerator]
    have hoff : ∑ column ∈ Finset.univ.erase row, jumpGenerator rate row column
        = ∑ column ∈ Finset.univ.erase row, rate row column :=
      Finset.sum_congr rfl fun column hcolumn ↦ by
        have hne : row ≠ column := fun heq ↦ (Finset.ne_of_mem_erase hcolumn) heq.symm
        simp [jumpGenerator, hne]
    rw [← hsplit, hdiag, hoff]
    simp

/-- The purely absorbing generator with a common killing rate: no jumps, uniform decay. -/
def uniformKilling [DecidableEq ι] (rate : ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun _ ↦ -rate)

/-- A nonnegative uniform killing rate gives a killing generator whose rows sum strictly
below zero unless the rate vanishes. -/
theorem killingGenerator_uniformKilling [DecidableEq ι] (rate : ℝ) (hrate : 0 ≤ rate) :
    KillingGenerator (uniformKilling (ι := ι) rate) where
  metzler := by
    intro row column hne
    simp [uniformKilling, Matrix.diagonal_apply_ne _ hne]
  rowSum_nonpos := by
    intro row
    have hrow : ∑ column, uniformKilling (ι := ι) rate row column = -rate := by
      simp [uniformKilling, Matrix.diagonal_apply]
    rw [hrow]
    linarith

end Witnesses

section Series

variable [DecidableEq ι]

private theorem expSeries_entry_summable (A : Matrix ι ι ℝ) (time : ℝ) (row column : ι) :
    Summable (fun power : ℕ ↦
      (((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)) row column) := by
  have hmatrix : Summable (fun power : ℕ ↦
      ((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)) :=
    NormedSpace.expSeries_summable' (time • A)
  exact Pi.summable.mp (Pi.summable.mp hmatrix row) column

private theorem expSeries_rowSum_term (A : Matrix ι ι ℝ) (time : ℝ) (row : ι) (power : ℕ) :
    ∑ column, (((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)) row column
      = ((power.factorial : ℝ)⁻¹) * (time ^ power * ∑ column, (A ^ power) row column) := by
  rw [smul_pow]
  simp [Finset.mul_sum]

/-- The row mass of the exact matrix exponential is the convergent scalar series of the row
masses of the matrix powers. -/
theorem exponential_rowSum_eq_tsum (A : Matrix ι ι ℝ) (time : ℝ) (row : ι) :
    ∑ column, matrixExponential A time row column
      = ∑' power : ℕ,
          ((power.factorial : ℝ)⁻¹) * (time ^ power * ∑ column, (A ^ power) row column) := by
  have hmatrix : Summable (fun power : ℕ ↦
      ((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)) :=
    NormedSpace.expSeries_summable' (time • A)
  have hrow : Summable (fun power : ℕ ↦
      (((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)) row) :=
    Pi.summable.mp hmatrix row
  have hpoint : ∀ column : ι, matrixExponential A time row column
      = ∑' power : ℕ,
          (((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)) row column := by
    intro column
    unfold matrixExponential
    rw [tsum_apply hmatrix, tsum_apply hrow]
  calc ∑ column, matrixExponential A time row column
      = ∑ column, ∑' power : ℕ,
          (((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)) row column :=
        Finset.sum_congr rfl fun column _ ↦ hpoint column
    _ = ∑' power : ℕ, ∑ column,
          (((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)) row column :=
        (Summable.tsum_finsetSum fun column _ ↦
          expSeries_entry_summable A time row column).symm
    _ = ∑' power : ℕ,
          ((power.factorial : ℝ)⁻¹) * (time ^ power * ∑ column, (A ^ power) row column) :=
        tsum_congr fun power ↦ expSeries_rowSum_term A time row power

/-- The scalar series of row masses converges. -/
theorem exponential_rowSum_summable (A : Matrix ι ι ℝ) (time : ℝ) (row : ι) :
    Summable (fun power : ℕ ↦
      ((power.factorial : ℝ)⁻¹) * (time ^ power * ∑ column, (A ^ power) row column)) := by
  have hfinite : Summable (fun power : ℕ ↦
      ∑ column, (((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)) row column) :=
    summable_sum fun column _ ↦ expSeries_entry_summable A time row column
  exact hfinite.congr fun power ↦ expSeries_rowSum_term A time row power

/-- The real exponential is the scalar factorial series; stated here in the multiplicative
form used by the row-mass comparison. -/
theorem tsum_factorial_pow (value : ℝ) :
    ∑' power : ℕ, ((power.factorial : ℝ)⁻¹) * value ^ power = Real.exp value := by
  rw [Real.exp_eq_exp_ℝ]
  simp only [NormedSpace.exp_eq_tsum, smul_eq_mul]

/-- An entrywise-nonnegative matrix whose rows sum to at most `bound` has powers whose rows
sum to at most `bound ^ k`. -/
theorem matrix_pow_rowSum_le (M : Matrix ι ι ℝ) (hM : ∀ row column, 0 ≤ M row column)
    (bound : ℝ) (hbound : 0 ≤ bound) (hrow : ∀ row, ∑ column, M row column ≤ bound)
    (power : ℕ) (row : ι) : ∑ column, (M ^ power) row column ≤ bound ^ power := by
  induction power with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    have hpow := matrix_pow_apply_nonneg_of_nonneg M hM k
    have hexpand : ∑ column, (M ^ (k + 1)) row column
        = ∑ middle, (M ^ k) row middle * ∑ column, M middle column := by
      simp only [pow_succ, Matrix.mul_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hexpand, pow_succ]
    calc ∑ middle, (M ^ k) row middle * ∑ column, M middle column
        ≤ ∑ middle, (M ^ k) row middle * bound :=
          Finset.sum_le_sum fun middle _ ↦
            mul_le_mul_of_nonneg_left (hrow middle) (hpow row middle)
      _ = (∑ middle, (M ^ k) row middle) * bound := by rw [Finset.sum_mul]
      _ ≤ bound ^ k * bound := mul_le_mul_of_nonneg_right ih hbound

/-- An entrywise-nonnegative matrix whose rows sum to at most `bound` has an exponential
whose rows sum to at most `Real.exp (time * bound)`. -/
theorem exponential_rowSum_le_exp (M : Matrix ι ι ℝ) (hM : ∀ row column, 0 ≤ M row column)
    (bound : ℝ) (hbound : 0 ≤ bound) (hrow : ∀ row, ∑ column, M row column ≤ bound)
    (time : ℝ) (htime : 0 ≤ time) (row : ι) :
    ∑ column, matrixExponential M time row column ≤ Real.exp (time * bound) := by
  rw [exponential_rowSum_eq_tsum, ← tsum_factorial_pow (time * bound)]
  refine Summable.tsum_le_tsum (fun power ↦ ?_) (exponential_rowSum_summable M time row) ?_
  · have hfac : (0 : ℝ) ≤ ((power.factorial : ℝ)⁻¹) :=
      inv_nonneg.mpr (Nat.cast_nonneg power.factorial)
    have hinner : time ^ power * ∑ column, (M ^ power) row column
        ≤ (time * bound) ^ power := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (matrix_pow_rowSum_le M hM bound hbound hrow power row)
        (pow_nonneg htime power)
    exact mul_le_mul_of_nonneg_left hinner hfac
  · simpa [smul_eq_mul] using NormedSpace.expSeries_summable' (𝕂 := ℝ) (time * bound)

/-- A scalar diagonal shift factors out of the exact matrix exponential. -/
theorem matrixExponential_scalar_shift (A : Matrix ι ι ℝ) (scalar time : ℝ) :
    matrixExponential (A + scalar • (1 : Matrix ι ι ℝ)) time
      = Real.exp (time * scalar) • matrixExponential A time := by
  have decomposition : time • (A + scalar • (1 : Matrix ι ι ℝ))
      = (time * scalar) • (1 : Matrix ι ι ℝ) + time • A := by
    rw [smul_add, smul_smul, add_comm]
  have commuting : Commute ((time * scalar) • (1 : Matrix ι ι ℝ)) (time • A) :=
    (Commute.one_left (time • A)).smul_left (time * scalar)
  have hscalar : NormedSpace.exp ℝ ((time * scalar) • (1 : Matrix ι ι ℝ))
      = Real.exp (time * scalar) • (1 : Matrix ι ι ℝ) := by
    rw [show ((time * scalar) • (1 : Matrix ι ι ℝ))
        = Matrix.diagonal (fun _ : ι ↦ time * scalar) by
      ext r s
      by_cases h : r = s <;> simp [h]]
    rw [Matrix.exp_diagonal]
    ext r s
    by_cases h : r = s <;> simp [h, Real.exp_eq_exp_ℝ]
  rw [matrixExponential_eq_normedSpace_exp, decomposition,
    Matrix.exp_add_of_commute ℝ _ _ commuting, hscalar,
    ← matrixExponential_eq_normedSpace_exp, smul_mul_assoc, one_mul]

/-- **The exact semigroup of a finite killing generator is substochastic.**  Entries are
nonnegative by the Metzler positivity of the corpus, and no row creates mass: this is the
operator that NOTE1 (20) applies to an ancestral configuration vector. -/
theorem matrixExponential_substochastic (Q : Matrix ι ι ℝ) (hQ : KillingGenerator Q)
    (time : ℝ) (htime : 0 ≤ time) : SubstochasticMatrix (matrixExponential Q time) where
  entry_nonneg := fun row column ↦
    matrixExponential_apply_nonneg_of_metzler Q hQ.metzler time htime row column
  rowSum_le_one := by
    intro row
    set shift : ℝ := matrixMetzlerShift Q
    have hshift : 0 ≤ shift := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    have hnonneg : ∀ r c, 0 ≤ (Q + shift • (1 : Matrix ι ι ℝ)) r c :=
      matrix_add_metzlerShift_nonneg Q hQ.metzler
    have hrowbound : ∀ r, ∑ c, (Q + shift • (1 : Matrix ι ι ℝ)) r c ≤ shift := by
      intro r
      have hone : ∑ c, (shift • (1 : Matrix ι ι ℝ)) r c = shift := by
        simp [Matrix.one_apply]
      have hsplit : ∑ c, (Q + shift • (1 : Matrix ι ι ℝ)) r c
          = (∑ c, Q r c) + ∑ c, (shift • (1 : Matrix ι ι ℝ)) r c := by
        simp [Matrix.add_apply, Finset.sum_add_distrib]
      rw [hsplit, hone]
      linarith [hQ.rowSum_nonpos r]
    have hshifted := exponential_rowSum_le_exp (Q + shift • (1 : Matrix ι ι ℝ)) hnonneg
      shift hshift hrowbound time htime row
    rw [matrixExponential_scalar_shift Q shift time] at hshifted
    have hfactor : ∑ column, (Real.exp (time * shift) • matrixExponential Q time) row column
        = Real.exp (time * shift) * ∑ column, matrixExponential Q time row column := by
      simp [Finset.mul_sum]
    rw [hfactor] at hshifted
    have hpos : 0 < Real.exp (time * shift) := Real.exp_pos _
    nlinarith [hshifted, hpos]

/-- A chronological history of epochs, each an exponential of its own killing generator run
for its own nonnegative duration, composes to a substochastic operator. -/
theorem substochastic_epochProduct (epochs : List (Matrix ι ι ℝ × ℝ))
    (hepochs : ∀ epoch ∈ epochs, KillingGenerator epoch.1 ∧ 0 ≤ epoch.2) :
    SubstochasticMatrix (epochs.map (fun epoch ↦ matrixExponential epoch.1 epoch.2)).prod := by
  refine substochastic_listProd _ ?_
  intro P hP
  obtain ⟨epoch, hmem, rfl⟩ := List.mem_map.mp hP
  obtain ⟨hgen, hduration⟩ := hepochs epoch hmem
  exact matrixExponential_substochastic epoch.1 hgen epoch.2 hduration

/-- **A conservative generator loses no mass.**  When every row of `Q` sums to zero, every row
of the exact exponential sums to one at every time, so the constant vector is preserved. -/
theorem exponential_rowSum_eq_one (Q : Matrix ι ι ℝ)
    (hzero : ∀ row, ∑ column, Q row column = 0) (time : ℝ) (row : ι) :
    ∑ column, matrixExponential Q time row column = 1 := by
  have hpow : ∀ power : ℕ, ∀ r : ι,
      ∑ column, (Q ^ (power + 1)) r column = 0 := by
    intro power r
    have hexpand : ∑ column, (Q ^ (power + 1)) r column
        = ∑ middle, (Q ^ power) r middle * ∑ column, Q middle column := by
      simp only [pow_succ, Matrix.mul_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hexpand]
    exact Finset.sum_eq_zero fun middle _ ↦ by rw [hzero middle, mul_zero]
  rw [exponential_rowSum_eq_tsum]
  have hterm : ∀ power : ℕ,
      ((power.factorial : ℝ)⁻¹) * (time ^ power * ∑ column, (Q ^ power) row column)
        = if power = 0 then (1 : ℝ) else 0 := by
    intro power
    cases power with
    | zero => simp [Matrix.one_apply]
    | succ k => simp [hpow k row]
  rw [tsum_congr hterm]
  exact tsum_ite_eq 0 (1 : ℝ)

/-- The conservative case in vector form: the constant vector is a fixed point of the exact
semigroup of a generator whose rows sum to zero, so total mass is carried forward exactly. -/
theorem matrixExponential_mulVec_const (Q : Matrix ι ι ℝ)
    (hzero : ∀ row, ∑ column, Q row column = 0) (time : ℝ) :
    (matrixExponential Q time).mulVec (fun _ ↦ (1 : ℝ)) = fun _ ↦ (1 : ℝ) := by
  funext row
  simpa [Matrix.mulVec, dotProduct] using exponential_rowSum_eq_one Q hzero time row

/-- The uniformization operator `1 + λ⁻¹ • Q` of (26) is substochastic whenever the
uniformization rate dominates every exit rate. -/
theorem substochastic_uniformization (Q : Matrix ι ι ℝ) (hQ : KillingGenerator Q)
    (uniformRate : ℝ) (hpos : 0 < uniformRate)
    (hdominates : ∀ row, -Q row row ≤ uniformRate) :
    SubstochasticMatrix ((1 : Matrix ι ι ℝ) + uniformRate⁻¹ • Q) where
  entry_nonneg := by
    intro row column
    by_cases h : row = column
    · subst h
      have hentry : ((1 : Matrix ι ι ℝ) + uniformRate⁻¹ • Q) row row
          = 1 + uniformRate⁻¹ * Q row row := by
        simp
      rw [hentry]
      have hle : -Q row row ≤ uniformRate := hdominates row
      have hinv : 0 < uniformRate⁻¹ := inv_pos.mpr hpos
      have hkey : uniformRate⁻¹ * (-Q row row) ≤ uniformRate⁻¹ * uniformRate :=
        mul_le_mul_of_nonneg_left hle hinv.le
      rw [inv_mul_cancel₀ (ne_of_gt hpos)] at hkey
      nlinarith [hkey]
    · have hentry : ((1 : Matrix ι ι ℝ) + uniformRate⁻¹ • Q) row column
          = uniformRate⁻¹ * Q row column := by
        simp [h]
      rw [hentry]
      exact mul_nonneg (inv_nonneg.mpr hpos.le) (hQ.metzler row column h)
  rowSum_le_one := by
    intro row
    have hsplit : ∑ column, ((1 : Matrix ι ι ℝ) + uniformRate⁻¹ • Q) row column
        = (∑ column, (1 : Matrix ι ι ℝ) row column)
          + uniformRate⁻¹ * ∑ column, Q row column := by
      simp [Matrix.add_apply, Finset.sum_add_distrib, Finset.mul_sum]
    have hone : ∑ column, (1 : Matrix ι ι ℝ) row column = 1 := by
      simp [Matrix.one_apply]
    rw [hsplit, hone]
    have hdeficit : uniformRate⁻¹ * ∑ column, Q row column ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hpos.le) (hQ.rowSum_nonpos row)
    linarith

end Series

end Descent.Portability.SubstochasticGeneratorSemigroup
