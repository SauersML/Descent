/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Calibrator

/-!
# Failure of spectral sufficiency for non-Gaussian product priors

This file formalizes the algebraic certificate behind the negative answer to Question S.
There are two rigid bases: the eigenbasis of a covariance matrix and the coordinate basis in
which a non-Gaussian prior factorizes.  A spectrum forgets their relative orientation.

The main result is dimension- and order-general.  If independent centered coordinates have common
order-`q` cumulant `kappa` and are mixed by a matrix `L`, the squared Frobenius norm of the
resulting order-`q` cumulant tensor is

`kappa ^ 2 * sum i, sum j, ((L.transpose * L) i j) ^ q`.

Thus each nonzero scalar cumulant exposes the corresponding parallel-edge traffic observable.
At order two this is the spectral two-cycle.  From order three onward it can depend on covariance
orientation.  The second part gives exact two-dimensional witnesses: a diagonal block and its
forty-five-degree rotation have the same characteristic polynomial at every parameter value, but
different entrywise-cube and entrywise-fourth-power invariants.  The cubic low-SNR separation is
`11 / 24` for a skewed sparse prior, while the quartic separation is `49 / 96` for a symmetric
Rademacher prior.

No free-entropy limit theorem is assumed as a parameter here.  The declarations below prove the
finite-dimensional invariant and the coefficient separation on which such a theorem must act.
They therefore isolate the genuinely new mathematical obstruction without laundering the
adaptive-interpolation step.

## Biological interpretation

Take `L` to be a square root of a linkage-disequilibrium covariance matrix.  The input coordinates
are locus effects in the reference-allele basis.  A skewed sparse architecture can expose the
cubic invariant, while a symmetric non-Gaussian architecture can expose the quartic invariant.
More generally, every nonzero higher cumulant detects the matching LD traffic observable.  The
spectrum measures LD strength; these entrywise power sums also measure how LD eigenvectors are
oriented relative to loci.  This is the basis information that a spectral portability summary
discards.
-/

open scoped BigOperators Matrix

section CumulantContractions

variable {Row Locus : Type*} [Fintype Row] [Fintype Locus]

/-- Move one finite-sum index through a pair of indices. -/
private theorem sum_pair_out
    {A I J : Type*} [Fintype A] [Fintype I] [Fintype J] (f : A → I → J → ℝ) :
    (∑ a, ∑ i, ∑ j, f a i j) = ∑ i, ∑ j, ∑ a, f a i j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]

/-- A five-index finite Fubini permutation used by the third-order contraction proof. -/
private theorem sum_five_rotate
    {A B C I J : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype I] [Fintype J]
    (f : A → B → C → I → J → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ i, ∑ j, f a b c i j) =
      ∑ i, ∑ j, ∑ a, ∑ b, ∑ c, f a b c i j := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ i, ∑ j, f a b c i j) =
        ∑ a, ∑ b, ∑ i, ∑ j, ∑ c, f a b c i j := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact sum_pair_out (fun c i j ↦ f a b c i j)
    _ = ∑ a, ∑ i, ∑ j, ∑ b, ∑ c, f a b c i j := by
      apply Finset.sum_congr rfl
      intro a ha
      exact sum_pair_out (fun b i j ↦ ∑ c, f a b c i j)
    _ = ∑ i, ∑ j, ∑ a, ∑ b, ∑ c, f a b c i j := by
      exact sum_pair_out (fun a i j ↦ ∑ b, ∑ c, f a b c i j)

/-- A six-index finite Fubini permutation used by the fourth-order contraction proof. -/
private theorem sum_six_rotate
    {A B C D I J : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Fintype I] [Fintype J] (f : A → B → C → D → I → J → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ i, ∑ j, f a b c d i j) =
      ∑ i, ∑ j, ∑ a, ∑ b, ∑ c, ∑ d, f a b c d i j := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ i, ∑ j, f a b c d i j) =
        ∑ a, ∑ b, ∑ c, ∑ i, ∑ j, ∑ d, f a b c d i j := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      exact sum_pair_out (fun d i j ↦ f a b c d i j)
    _ = ∑ a, ∑ b, ∑ i, ∑ j, ∑ c, ∑ d, f a b c d i j := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact sum_pair_out (fun c i j ↦ ∑ d, f a b c d i j)
    _ = ∑ a, ∑ i, ∑ j, ∑ b, ∑ c, ∑ d, f a b c d i j := by
      apply Finset.sum_congr rfl
      intro a ha
      exact sum_pair_out (fun b i j ↦ ∑ c, ∑ d, f a b c d i j)
    _ = ∑ i, ∑ j, ∑ a, ∑ b, ∑ c, ∑ d, f a b c d i j := by
      exact sum_pair_out (fun a i j ↦ ∑ b, ∑ c, ∑ d, f a b c d i j)

/-- Expansion of the square of a finite sum. -/
private theorem sum_sq_expand {I : Type*} [Fintype I] (f : I → ℝ) :
    (∑ i, f i) ^ 2 = ∑ i, ∑ j, f i * f j := by
  simpa only [pow_two] using Fintype.sum_mul_sum f f

/-! ### The cumulant contraction in arbitrary order -/

/-- Order-`q` cumulant tensor obtained by mixing independent coordinates with common scalar
cumulant `kappa`.  Indexing tensor legs by `Fin q` makes the construction uniform in `q`. -/
noncomputable def pushedCumulantTensor
    (order : ℕ) (mixing : Matrix Row Locus ℝ) (kappa : ℝ)
    (indices : Fin order → Row) : ℝ :=
  kappa * ∑ locus, ∏ leg, mixing (indices leg) locus

/-- Squared Frobenius norm of an arbitrary-order tensor. -/
noncomputable def cumulantTensorEnergy
    (order : ℕ) (tensor : (Fin order → Row) → ℝ) : ℝ :=
  ∑ indices, tensor indices ^ 2

/-- The two-vertex, `order`-parallel-edge traffic observable.

Empirical status: UNTESTED. The sum is algebra on a covariance matrix. The empirical
claim in its neighbourhood -- that this quantity separates LD matrices that the spectrum
cannot tell apart -- is proved below on explicit witnesses, not measured on data. -/
noncomputable def entryPowerSum
    (covariance : Matrix Locus Locus ℝ) (order : ℕ) : ℝ :=
  ∑ left, ∑ right, covariance left right ^ order

/-- **All-order cumulant orientation identity.**  For every tensor order, the squared energy
of the pushed-forward diagonal cumulant tensor is the corresponding parallel-edge traffic
observable of the Gram covariance, multiplied by the squared scalar cumulant. -/
theorem cumulantTensorEnergy_pushedCumulantTensor
    (order : ℕ) (mixing : Matrix Row Locus ℝ) (kappa : ℝ) :
    cumulantTensorEnergy order (pushedCumulantTensor order mixing kappa) =
      kappa ^ 2 * entryPowerSum (mixing.transpose * mixing) order := by
  classical
  unfold cumulantTensorEnergy pushedCumulantTensor entryPowerSum
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  calc
    (∑ indices : Fin order → Row,
        (kappa * ∑ locus, ∏ leg, mixing (indices leg) locus) ^ 2) =
        kappa ^ 2 * ∑ indices : Fin order → Row,
          ∑ left, ∑ right,
            (∏ leg, mixing (indices leg) left) *
              ∏ leg, mixing (indices leg) right := by
      simp_rw [mul_pow, sum_sq_expand]
      rw [Finset.mul_sum]
    _ = kappa ^ 2 * ∑ left, ∑ right,
        ∑ indices : Fin order → Row,
          (∏ leg, mixing (indices leg) left) *
            ∏ leg, mixing (indices leg) right := by
      rw [sum_pair_out]
    _ = kappa ^ 2 * ∑ left, ∑ right,
        (∑ row, mixing row left * mixing row right) ^ order := by
      congr 1
      apply Finset.sum_congr rfl
      intro left _
      apply Finset.sum_congr rfl
      intro right _
      calc
        (∑ indices : Fin order → Row,
            (∏ leg, mixing (indices leg) left) *
              ∏ leg, mixing (indices leg) right) =
            ∑ indices : Fin order → Row,
              ∏ leg, mixing (indices leg) left * mixing (indices leg) right := by
          apply Finset.sum_congr rfl
          intro indices _
          rw [Finset.prod_mul_distrib]
        _ = ∏ _leg : Fin order, ∑ row, mixing row left * mixing row right := by
          rw [Fintype.prod_sum]
        _ = (∑ row, mixing row left * mixing row right) ^ order := by simp
    _ = kappa ^ 2 *
        ∑ left, ∑ right, (∑ x, mixing x left * mixing x right) ^ order := rfl

/-- If the scalar cumulant vanishes, its pushed-forward tensor has zero energy at every order and
for every covariance orientation. -/
theorem cumulantTensorEnergy_pushedCumulantTensor_zero
    (order : ℕ) (mixing : Matrix Row Locus ℝ) :
    cumulantTensorEnergy order (pushedCumulantTensor order mixing 0) = 0 := by
  rw [cumulantTensorEnergy_pushedCumulantTensor]
  simp

/-- Expansion of the cube of a finite sum. -/
private theorem sum_cube_expand {I : Type*} [Fintype I] (f : I → ℝ) :
    (∑ i, f i) ^ 3 = ∑ i, ∑ j, ∑ k, f i * f j * f k := by
  rw [pow_three, Fintype.sum_mul_sum]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Expansion of the fourth power of a finite sum. -/
private theorem sum_fourth_expand {I : Type*} [Fintype I] (f : I → ℝ) :
    (∑ i, f i) ^ 4 = ∑ i, ∑ j, ∑ k, ∑ l, f i * f j * f k * f l := by
  calc
    (∑ i, f i) ^ 4 =
        ((∑ i, f i) * (∑ j, f j)) * ((∑ k, f k) * (∑ l, f l)) := by ring
    _ = (∑ i, ∑ j, f i * f j) * (∑ k, ∑ l, f k * f l) := by
      rw [Fintype.sum_mul_sum, Fintype.sum_mul_sum]
    _ = ∑ i, ∑ j, ∑ k, ∑ l, f i * f j * f k * f l := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      ring

/-- The third moment tensor obtained by applying `mixing` to independent centered coordinates
whose common scalar third moment is `kappa`. -/
noncomputable def pushedThirdMomentTensor
    (mixing : Matrix Row Locus ℝ) (kappa : ℝ) (a b c : Row) : ℝ :=
  kappa * ∑ i, mixing a i * mixing b i * mixing c i

/-- Squared Frobenius norm of a three-index tensor. -/
noncomputable def thirdTensorEnergy (tensor : Row → Row → Row → ℝ) : ℝ :=
  ∑ a, ∑ b, ∑ c, tensor a b c ^ 2

/-- The first non-spectral invariant seen by a skewed product prior: the sum of the cubes of all
entries of a covariance matrix. -/
noncomputable def entryCubeSum (covariance : Matrix Locus Locus ℝ) : ℝ :=
  ∑ i, ∑ j, covariance i j ^ 3

/-- The cubic observable is the order-three specialization of the all-order traffic sum. -/
theorem entryPowerSum_three (covariance : Matrix Locus Locus ℝ) :
    entryPowerSum covariance 3 = entryCubeSum covariance :=
  rfl

/-- The Gram covariance induced by a mixing matrix. -/
noncomputable def gramCovariance (mixing : Matrix Row Locus ℝ) : Matrix Locus Locus ℝ :=
  mixing.transpose * mixing

/-- **General third-moment orientation identity.**  The energy of the pushed-forward third
moment tensor is the entrywise-cube sum of the Gram covariance, multiplied by `kappa ^ 2`.

This is the dimension-free algebraic mechanism behind basis-sensitive low-SNR information. -/
theorem thirdTensorEnergy_pushedThirdMomentTensor
    (mixing : Matrix Row Locus ℝ) (kappa : ℝ) :
    thirdTensorEnergy (pushedThirdMomentTensor mixing kappa) =
      kappa ^ 2 * entryCubeSum (gramCovariance mixing) := by
  classical
  unfold thirdTensorEnergy pushedThirdMomentTensor entryCubeSum gramCovariance
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [mul_pow, sum_sq_expand, sum_cube_expand]
  simp_rw [Finset.mul_sum]
  rw [sum_five_rotate]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  ring

/-! ### The symmetric-prior obstruction at fourth order -/

/-- The fourth cumulant tensor obtained by applying `mixing` to independent centered
coordinates whose common scalar fourth cumulant is `kappa`. -/
noncomputable def pushedFourthCumulantTensor
    (mixing : Matrix Row Locus ℝ) (kappa : ℝ) (a b c d : Row) : ℝ :=
  kappa * ∑ i, mixing a i * mixing b i * mixing c i * mixing d i

/-- Squared Frobenius norm of a four-index tensor. -/
noncomputable def fourthTensorEnergy (tensor : Row → Row → Row → Row → ℝ) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, tensor a b c d ^ 2

/-- The orientation-sensitive invariant that remains available to symmetric non-Gaussian
product priors: the sum of the fourth powers of all covariance entries. -/
noncomputable def entryFourthSum (covariance : Matrix Locus Locus ℝ) : ℝ :=
  ∑ i, ∑ j, covariance i j ^ 4

/-- The quartic observable is the order-four specialization of the all-order traffic sum. -/
theorem entryPowerSum_four (covariance : Matrix Locus Locus ℝ) :
    entryPowerSum covariance 4 = entryFourthSum covariance :=
  rfl

/-- **General fourth-cumulant orientation identity.**  The energy of the pushed-forward fourth
cumulant tensor is the entrywise-fourth-power sum of the Gram covariance, multiplied by
`kappa ^ 2`.  Unlike the third-order obstruction, this survives symmetric sparse priors. -/
theorem fourthTensorEnergy_pushedFourthCumulantTensor
    (mixing : Matrix Row Locus ℝ) (kappa : ℝ) :
    fourthTensorEnergy (pushedFourthCumulantTensor mixing kappa) =
      kappa ^ 2 * entryFourthSum (gramCovariance mixing) := by
  classical
  unfold fourthTensorEnergy pushedFourthCumulantTensor entryFourthSum gramCovariance
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [mul_pow, sum_sq_expand, sum_fourth_expand]
  simp_rw [Finset.mul_sum]
  rw [sum_six_rotate]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- The power-`power` LD score of one locus.  Power two is the usual LD score; power four is
the per-locus statistic detecting symmetric non-Gaussian orientation effects.

Empirical status: UNTESTED. Power two is the standard LD score and is measured routinely
elsewhere; the fourth-power statistic named here has not been computed on any panel in this
development, and nothing below claims it has. -/
noncomputable def ldPowerScore
    (covariance : Matrix Locus Locus ℝ) (power : ℕ) (j : Locus) : ℝ :=
  ∑ i, covariance i j ^ power

/-- The fourth-order orientation invariant is the sum of per-locus fourth-power LD scores. -/
theorem entryFourthSum_eq_sum_ldPowerScore_four (covariance : Matrix Locus Locus ℝ) :
    entryFourthSum covariance = ∑ j, ldPowerScore covariance 4 j := by
  unfold entryFourthSum ldPowerScore
  rw [Finset.sum_comm]

end CumulantContractions

/-! ## An exactly isospectral two-dimensional witness -/

/-- A covariance block localized in the product-prior coordinate basis. -/
noncomputable def localizedCovarianceBlock (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, 0; 0, a + 1]

/-- The same covariance eigenvalues after a forty-five degree rotation. -/
noncomputable def rotatedCovarianceBlock (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a + 1 / 2, 1 / 2; 1 / 2, a + 1 / 2]

/-- Exact isospectrality for two-dimensional matrices, expressed without choosing or ordering
eigenvectors: their characteristic determinants agree at every spectral parameter. -/
def Isospectral2 (left right : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ spectralParameter : ℝ,
    Matrix.det (left - spectralParameter • 1) =
      Matrix.det (right - spectralParameter • 1)

/-- Characteristic determinant of the localized block. -/
theorem localizedCovarianceBlock_characteristicDeterminant (a spectralParameter : ℝ) :
    Matrix.det (localizedCovarianceBlock a - spectralParameter • 1) =
      (a - spectralParameter) * (a + 1 - spectralParameter) := by
  simp [localizedCovarianceBlock, Matrix.det_fin_two]

/-- Characteristic determinant of the rotated block.  Its factorization is identical to the
localized block's factorization, which is exact isospectrality rather than moment matching. -/
theorem rotatedCovarianceBlock_characteristicDeterminant (a spectralParameter : ℝ) :
    Matrix.det (rotatedCovarianceBlock a - spectralParameter • 1) =
      (a - spectralParameter) * (a + 1 - spectralParameter) := by
  simp [rotatedCovarianceBlock, Matrix.det_fin_two]
  ring

/-- The localized and rotated blocks are exactly isospectral for every value of `a`. -/
theorem localizedCovarianceBlock_isospectral_rotatedCovarianceBlock (a : ℝ) :
    Isospectral2 (localizedCovarianceBlock a) (rotatedCovarianceBlock a) := by
  intro spectralParameter
  rw [localizedCovarianceBlock_characteristicDeterminant,
    rotatedCovarianceBlock_characteristicDeterminant]

/-- **A spectral root of either block is `a` or `a + 1`.**

Both bounds below are read off this: the root is one of two values, and where each lands
follows from where `a` lands.  Stated separately, each carried its own case split on the
same factorisation. -/
theorem block_spectralParameter_eq_or
    (a spectralParameter : ℝ)
    (hroot : (a - spectralParameter) * (a + 1 - spectralParameter) = 0) :
    spectralParameter = a ∨ spectralParameter = a + 1 := by
  rcases mul_eq_zero.mp hroot with hroot | hroot
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- Every spectral root of either block is at least one when `1 ≤ a`. -/
theorem block_spectralParameter_ge_one
    (a spectralParameter : ℝ) (ha : 1 ≤ a)
    (hroot : (a - spectralParameter) * (a + 1 - spectralParameter) = 0) :
    1 ≤ spectralParameter := by
  rcases block_spectralParameter_eq_or a spectralParameter hroot with h | h <;> linarith

/-- Every spectral root of either block is at most three when `a ≤ 2`. -/
theorem block_spectralParameter_le_three
    (a spectralParameter : ℝ) (ha : a ≤ 2)
    (hroot : (a - spectralParameter) * (a + 1 - spectralParameter) = 0) :
    spectralParameter ≤ 3 := by
  rcases block_spectralParameter_eq_or a spectralParameter hroot with h | h <;> linarith

/-- Per-coordinate normalization of the entrywise cube invariant for a two-dimensional block. -/
noncomputable def blockEntryCubeMean (covariance : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  entryCubeSum covariance / 2

/-- Closed form of the orientation invariant for the localized block. -/
theorem blockEntryCubeMean_localizedCovarianceBlock (a : ℝ) :
    blockEntryCubeMean (localizedCovarianceBlock a) = (a ^ 3 + (a + 1) ^ 3) / 2 := by
  simp [blockEntryCubeMean, entryCubeSum, localizedCovarianceBlock, Fin.sum_univ_two]

/-- Closed form of the orientation invariant for the rotated block. -/
theorem blockEntryCubeMean_rotatedCovarianceBlock (a : ℝ) :
    blockEntryCubeMean (rotatedCovarianceBlock a) = (a + 1 / 2) ^ 3 + 1 / 8 := by
  simp [blockEntryCubeMean, entryCubeSum, rotatedCovarianceBlock, Fin.sum_univ_two]
  ring

/-- The two exactly isospectral blocks differ in their orientation invariant by an affine amount.
On the midpoint grid used for the uniform `[1, 3]` limiting spectrum, its average is `11 / 8`. -/
theorem blockEntryCubeMean_localized_sub_rotated (a : ℝ) :
    blockEntryCubeMean (localizedCovarianceBlock a) -
        blockEntryCubeMean (rotatedCovarianceBlock a) = 3 * a / 4 + 1 / 4 := by
  rw [blockEntryCubeMean_localizedCovarianceBlock,
    blockEntryCubeMean_rotatedCovarianceBlock]
  ring

/-- The midpoint block already realizes the continuum construction's exact mean separation. -/
theorem midpoint_blockEntryCubeMean_separation :
    blockEntryCubeMean (localizedCovarianceBlock (3 / 2)) -
        blockEntryCubeMean (rotatedCovarianceBlock (3 / 2)) = 11 / 8 := by
  rw [blockEntryCubeMean_localized_sub_rotated]
  norm_num

/-- Per-coordinate normalization of the entrywise fourth-power invariant for a block. -/
noncomputable def blockEntryFourthMean (covariance : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  entryFourthSum covariance / 2

/-- Closed form of the fourth-order orientation invariant for the localized block. -/
theorem blockEntryFourthMean_localizedCovarianceBlock (a : ℝ) :
    blockEntryFourthMean (localizedCovarianceBlock a) =
      (a ^ 4 + (a + 1) ^ 4) / 2 := by
  simp [blockEntryFourthMean, entryFourthSum, localizedCovarianceBlock, Fin.sum_univ_two]

/-- Closed form of the fourth-order orientation invariant for the rotated block. -/
theorem blockEntryFourthMean_rotatedCovarianceBlock (a : ℝ) :
    blockEntryFourthMean (rotatedCovarianceBlock a) =
      (a + 1 / 2) ^ 4 + 1 / 16 := by
  simp [blockEntryFourthMean, entryFourthSum, rotatedCovarianceBlock, Fin.sum_univ_two]
  ring

/-- The exactly isospectral blocks have distinct fourth-order orientation invariants throughout
the positive-definite parameter range.  The gap is a positive perfect square. -/
theorem blockEntryFourthMean_localized_sub_rotated (a : ℝ) :
    blockEntryFourthMean (localizedCovarianceBlock a) -
        blockEntryFourthMean (rotatedCovarianceBlock a) =
      3 / 2 * (a + 1 / 2) ^ 2 := by
  rw [blockEntryFourthMean_localizedCovarianceBlock,
    blockEntryFourthMean_rotatedCovarianceBlock]
  ring

/-- The midpoint construction has fourth-order per-coordinate separation exactly six. -/
theorem midpoint_blockEntryFourthMean_separation :
    blockEntryFourthMean (localizedCovarianceBlock (3 / 2)) -
        blockEntryFourthMean (rotatedCovarianceBlock (3 / 2)) = 6 := by
  rw [blockEntryFourthMean_localized_sub_rotated]
  norm_num

/-- The midpoint blocks have unequal fourth-order orientation invariants. -/
theorem midpoint_blockEntryFourthMean_ne :
    blockEntryFourthMean (localizedCovarianceBlock (3 / 2)) ≠
      blockEntryFourthMean (rotatedCovarianceBlock (3 / 2)) := by
  intro heq
  have hzero :
      blockEntryFourthMean (localizedCovarianceBlock (3 / 2)) -
          blockEntryFourthMean (rotatedCovarianceBlock (3 / 2)) = 0 := by
    rw [heq, sub_self]
  rw [midpoint_blockEntryFourthMean_separation] at hzero
  norm_num at hzero

/-- There is no characteristic-polynomial formula for the fourth-order invariant, even on the
same well-conditioned positive covariance blocks used by the third-order witness. -/
theorem no_isospectral_formula_for_blockEntryFourthMean :
    ¬ ∃ spectralFormula : ((ℝ → ℝ) → ℝ),
      ∀ covariance : Matrix (Fin 2) (Fin 2) ℝ,
        blockEntryFourthMean covariance =
          spectralFormula (fun spectralParameter ↦
            Matrix.det (covariance - spectralParameter • 1)) := by
  rintro ⟨spectralFormula, hspectral⟩
  have hsame :
      (fun spectralParameter : ℝ ↦
          Matrix.det (localizedCovarianceBlock (3 / 2) -
            spectralParameter • (1 : Matrix (Fin 2) (Fin 2) ℝ))) =
        fun spectralParameter : ℝ ↦
          Matrix.det (rotatedCovarianceBlock (3 / 2) -
            spectralParameter • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
    funext spectralParameter
    exact localizedCovarianceBlock_isospectral_rotatedCovarianceBlock
      (3 / 2) spectralParameter
  have heq :
      blockEntryFourthMean (localizedCovarianceBlock (3 / 2)) =
        blockEntryFourthMean (rotatedCovarianceBlock (3 / 2)) := by
    rw [hspectral, hspectral, hsame]
  have hzero :
      blockEntryFourthMean (localizedCovarianceBlock (3 / 2)) -
          blockEntryFourthMean (rotatedCovarianceBlock (3 / 2)) = 0 := by
    rw [heq, sub_self]
  rw [midpoint_blockEntryFourthMean_separation] at hzero
  norm_num at hzero

/-! ## The continuum block family and the exact Rademacher coefficient -/

/-- Per-coordinate fourth-order invariant of the localized block family, averaged uniformly
over offsets `a ∈ [1, 2]`. -/
noncomputable def localizedUniformFourthInvariant : ℝ :=
  ∫ a in (1 : ℝ)..2, blockEntryFourthMean (localizedCovarianceBlock a)

/-- Per-coordinate fourth-order invariant of the rotated block family, averaged uniformly over
offsets `a ∈ [1, 2]`. -/
noncomputable def rotatedUniformFourthInvariant : ℝ :=
  ∫ a in (1 : ℝ)..2, blockEntryFourthMean (rotatedCovarianceBlock a)

/-- **The integral of a quartic over `[1, 2]`, once.**

Both traffic invariants below are this integral at different coefficients.  Written out at
each one, the antiderivative and its five derivative steps appeared twice verbatim, which
made a shared computation look like two independent ones. -/
theorem integral_quartic_one_two (c₄ c₃ c₂ c₁ c₀ : ℝ) :
    (∫ a in (1 : ℝ)..2, (c₄ * a ^ 4 + c₃ * a ^ 3 + c₂ * a ^ 2 + c₁ * a ^ 1 + c₀ * a ^ 0)) =
      31 / 5 * c₄ + 15 / 4 * c₃ + 7 / 3 * c₂ + 3 / 2 * c₁ + c₀ := by
  have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) 2,
      HasDerivAt (fun a : ℝ ↦ c₄ / 5 * a ^ 5 + c₃ / 4 * a ^ 4 + c₂ / 3 * a ^ 3 +
          c₁ / 2 * a ^ 2 + c₀ * a ^ 1)
        (c₄ * x ^ 4 + c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x ^ 1 + c₀ * x ^ 0) x := by
    intro x _
    have h := ((((hasDerivAt_pow 5 x).const_mul (c₄ / 5)).add
        ((hasDerivAt_pow 4 x).const_mul (c₃ / 4))).add
        ((hasDerivAt_pow 3 x).const_mul (c₂ / 3))).add
        ((hasDerivAt_pow 2 x).const_mul (c₁ / 2)) |>.add
        ((hasDerivAt_pow 1 x).const_mul c₀)
    convert h using 1
    push_cast
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) 1 2)]
  norm_num
  all_goals ring

/-- The localized block family has fourth-order traffic invariant `121 / 5`. -/
theorem localizedUniformFourthInvariant_eq :
    localizedUniformFourthInvariant = 121 / 5 := by
  unfold localizedUniformFourthInvariant
  simp_rw [blockEntryFourthMean_localizedCovarianceBlock]
  have hintegrand :
      (fun a : ℝ ↦ (a ^ 4 + (a + 1) ^ 4) / 2) =
        fun a : ℝ ↦ 1 * a ^ 4 + 2 * a ^ 3 + 3 * a ^ 2 + 2 * a ^ 1 + (1 / 2) * a ^ 0 := by
    funext a
    ring
  rw [hintegrand, integral_quartic_one_two]
  norm_num

/-- The rotated block family has fourth-order traffic invariant `723 / 40`. -/
theorem rotatedUniformFourthInvariant_eq :
    rotatedUniformFourthInvariant = 723 / 40 := by
  unfold rotatedUniformFourthInvariant
  simp_rw [blockEntryFourthMean_rotatedCovarianceBlock]
  have hintegrand :
      (fun a : ℝ ↦ (a + 1 / 2) ^ 4 + 1 / 16) =
        fun a : ℝ ↦ 1 * a ^ 4 + 2 * a ^ 3 + (3 / 2) * a ^ 2 + (1 / 2) * a ^ 1
          + (1 / 8) * a ^ 0 := by
    funext a
    ring
  rw [hintegrand, integral_quartic_one_two]
  norm_num

/-- Exact continuum separation of the fourth-order traffic invariant. -/
theorem localizedUniformFourthInvariant_sub_rotated :
    localizedUniformFourthInvariant - rotatedUniformFourthInvariant = 49 / 8 := by
  rw [localizedUniformFourthInvariant_eq, rotatedUniformFourthInvariant_eq]
  norm_num

/-- The orientation-sensitive part of the fourth low-SNR mutual-information coefficient. -/
noncomputable def lowSNRFourthOrientationCoefficient
    (fourthCumulant h4 : ℝ) : ℝ :=
  -(fourthCumulant ^ 2 / 48 * h4)

/-- Reference evaluation: the body is fixed at a point, not merely bounded or shown invariant.
An inequality or an invariance leaves a family of bodies satisfying it; a value does not. -/
theorem lowSNRFourthOrientationCoefficient_at_reference_point :
    lowSNRFourthOrientationCoefficient 2 2 = -1 / 6 := by
  norm_num [lowSNRFourthOrientationCoefficient]


/-- The fourth spectral moment produced by the rectangular Gaussian design.  Here `c` is the
inverse aspect ratio and `m1`, ..., `m4` are the first four covariance spectral moments. -/
noncomputable def gaussianDesignFourthSpectralMoment
    (c m1 m2 m3 m4 : ℝ) : ℝ :=
  m4 + c * (4 * m1 * m3 + 2 * m2 ^ 2) +
    6 * c ^ 2 * m1 ^ 2 * m2 + c ^ 3 * m1 ^ 4

/-- Reference evaluation: the body is fixed at a point, not merely bounded or shown invariant.
An inequality or an invariance leaves a family of bodies satisfying it; a value does not. -/
theorem gaussianDesignFourthSpectralMoment_at_reference_point :
    gaussianDesignFourthSpectralMoment 2 2 2 2 2 = 370 := by
  norm_num [gaussianDesignFourthSpectralMoment]


/-- Complete fourth low-SNR coefficient: a spectral Wishart term plus the fourth-cumulant
traffic term.  This definition keeps the two information channels visibly separate. -/
noncomputable def lowSNRFourthCoefficient
    (c variance fourthCumulant m1 m2 m3 m4 h4 : ℝ) : ℝ :=
  -(variance ^ 4 / 8 * gaussianDesignFourthSpectralMoment c m1 m2 m3 m4) -
    fourthCumulant ^ 2 / 48 * h4

/-- At fixed spectral moments, orientation changes the complete fourth coefficient by precisely
the fourth-cumulant square times the change in fourth-power traffic. -/
theorem lowSNRFourthCoefficient_sub_of_spectral_match
    (c variance fourthCumulant m1 m2 m3 m4 h4Left h4Right : ℝ) :
    lowSNRFourthCoefficient c variance fourthCumulant m1 m2 m3 m4 h4Right -
        lowSNRFourthCoefficient c variance fourthCumulant m1 m2 m3 m4 h4Left =
      fourthCumulant ^ 2 / 48 * (h4Left - h4Right) := by
  unfold lowSNRFourthCoefficient
  ring

/-- For a Rademacher prior, whose fourth cumulant is `-2`, the rotated design's fourth-order
mutual-information coefficient exceeds the localized design's by exactly `49 / 96`. -/
theorem rademacher_lowSNRFourthCoefficient_rotated_sub_localized :
    lowSNRFourthOrientationCoefficient (-2) rotatedUniformFourthInvariant -
      lowSNRFourthOrientationCoefficient (-2) localizedUniformFourthInvariant = 49 / 96 := by
  unfold lowSNRFourthOrientationCoefficient
  calc
    -((-2 : ℝ) ^ 2 / 48 * rotatedUniformFourthInvariant) -
          -((-2 : ℝ) ^ 2 / 48 * localizedUniformFourthInvariant) =
        (localizedUniformFourthInvariant - rotatedUniformFourthInvariant) / 12 := by ring
    _ = 49 / 96 := by rw [localizedUniformFourthInvariant_sub_rotated]; norm_num

/-- The same `49 / 96` separation for the complete fourth coefficient, uniformly in the aspect
ratio and all four common spectral moments. -/
theorem rademacher_fullLowSNRFourthCoefficient_rotated_sub_localized
    (c m1 m2 m3 m4 : ℝ) :
    lowSNRFourthCoefficient c 1 (-2) m1 m2 m3 m4 rotatedUniformFourthInvariant -
        lowSNRFourthCoefficient c 1 (-2) m1 m2 m3 m4 localizedUniformFourthInvariant =
      49 / 96 := by
  rw [lowSNRFourthCoefficient_sub_of_spectral_match]
  rw [localizedUniformFourthInvariant_sub_rotated]
  norm_num

/-! ## The order-two coincidence -/

/-- Entrywise square sum, the two-parallel-edge traffic observable. -/
noncomputable def entrySquareSum {Locus : Type*} [Fintype Locus]
    (covariance : Matrix Locus Locus ℝ) : ℝ :=
  ∑ i, ∑ j, covariance i j ^ 2

/-- The quadratic observable is the order-two specialization of the all-order traffic sum. -/
theorem entryPowerSum_two {Locus : Type*} [Fintype Locus]
    (covariance : Matrix Locus Locus ℝ) :
    entryPowerSum covariance 2 = entrySquareSum covariance :=
  rfl

/-- For a symmetric covariance, the two-parallel-edge traffic observable is exactly the
spectral two-cycle `Tr(Σ²)`.  This is the low-order coincidence that fails from order three on. -/
theorem entrySquareSum_eq_trace_sq_of_symmetric
    {Locus : Type*} [Fintype Locus] [DecidableEq Locus]
    (covariance : Matrix Locus Locus ℝ)
    (hsymmetric : ∀ i j, covariance j i = covariance i j) :
    entrySquareSum covariance = Matrix.trace (covariance * covariance) := by
  classical
  change (∑ i, ∑ j, covariance i j ^ 2) =
    ∑ i, ∑ j, covariance i j * covariance j i
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hsymmetric]
  ring

/-! ## The low-SNR coefficient and the Question S certificate -/

/-- Three equiprobable atoms realizing the centered form of the sparse prior
`(2 / 3) delta_(-1) + (1 / 3) delta_2`.  Repeating `-1` twice avoids introducing a
measure-theoretic wrapper around an elementary finite law. -/
noncomputable def centeredSparsePriorAtom : Fin 3 → ℝ := ![-1, -1, 2]

/-- The centered sparse prior has mean zero. -/
theorem centeredSparsePriorAtom_mean :
    (∑ i, centeredSparsePriorAtom i) / 3 = 0 := by
  norm_num [centeredSparsePriorAtom, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons]

/-- The centered sparse prior has variance two. -/
theorem centeredSparsePriorAtom_secondMoment :
    (∑ i, centeredSparsePriorAtom i ^ 2) / 3 = 2 := by
  norm_num [centeredSparsePriorAtom, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons]

/-- The centered sparse prior has third moment two, so it detects covariance orientation at the
first non-spectral low-SNR order. -/
theorem centeredSparsePriorAtom_thirdMoment :
    (∑ i, centeredSparsePriorAtom i ^ 3) / 3 = 2 := by
  norm_num [centeredSparsePriorAtom, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons]

/-- The cubic low-SNR coefficient after the spectral terms and the orientation term are
separated.  `m1`, `m2`, and `m3` are spectral moments; `h3` is the entrywise-cube invariant. -/
noncomputable def lowSNRThirdCoefficient
    (aspect variance thirdMoment m1 m2 m3 h3 : ℝ) : ℝ :=
  variance ^ 3 / 6 *
      (m3 + 3 * m1 * m2 / aspect + m1 ^ 3 / aspect ^ 2) -
    thirdMoment ^ 2 / 12 * h3

/-- At zero aspect both aspect-scaled moment terms are Mathlib junk `0`, so the coefficient
drops the cross-moment structure entirely and reports only the diagonal third moment against
the orientation term. -/
theorem lowSNRThirdCoefficient_at_zero_aspect_is_junk
    (variance thirdMoment m1 m2 m3 h3 : ℝ) :
    lowSNRThirdCoefficient 0 variance thirdMoment m1 m2 m3 h3
      = variance ^ 3 / 6 * m3 - thirdMoment ^ 2 / 12 * h3 := by
  simp [lowSNRThirdCoefficient]


/-- At fixed spectrum, changing orientation changes the cubic coefficient by exactly the squared
third moment times the change in the entrywise-cube invariant. -/
theorem lowSNRThirdCoefficient_sub_of_spectral_match
    (aspect variance thirdMoment m1 m2 m3 h3Left h3Right : ℝ) :
    lowSNRThirdCoefficient aspect variance thirdMoment m1 m2 m3 h3Right -
        lowSNRThirdCoefficient aspect variance thirdMoment m1 m2 m3 h3Left =
      thirdMoment ^ 2 / 12 * (h3Left - h3Right) := by
  unfold lowSNRThirdCoefficient
  ring

/-- **Question S coefficient certificate.**  For the centered sparse prior with variance `2` and
third moment `2`, the rotated orientation's cubic information coefficient exceeds the localized
orientation's coefficient by exactly `11 / 24`, despite exact isospectrality. -/
theorem sparsePrior_lowSNRThirdCoefficient_rotated_sub_localized
    (aspect m1 m2 m3 : ℝ) :
    lowSNRThirdCoefficient aspect 2 2 m1 m2 m3
        (blockEntryCubeMean (rotatedCovarianceBlock (3 / 2))) -
      lowSNRThirdCoefficient aspect 2 2 m1 m2 m3
        (blockEntryCubeMean (localizedCovarianceBlock (3 / 2))) = 11 / 24 := by
  rw [lowSNRThirdCoefficient_sub_of_spectral_match]
  rw [midpoint_blockEntryCubeMean_separation]
  norm_num

/-- There is no spectrum-only representation of the entrywise-cube invariant, already among
positive two-dimensional covariance blocks with eigenvalues in `[1, 3]`. -/
theorem exists_isospectral_blocks_with_distinct_entryCubeMean :
    ∃ localized rotated : Matrix (Fin 2) (Fin 2) ℝ,
      Isospectral2 localized rotated ∧
        blockEntryCubeMean localized ≠ blockEntryCubeMean rotated := by
  refine ⟨localizedCovarianceBlock (3 / 2), rotatedCovarianceBlock (3 / 2),
    localizedCovarianceBlock_isospectral_rotatedCovarianceBlock (3 / 2), ?_⟩
  intro heq
  have hzero :
      blockEntryCubeMean (localizedCovarianceBlock (3 / 2)) -
          blockEntryCubeMean (rotatedCovarianceBlock (3 / 2)) = 0 := by
    rw [heq, sub_self]
  rw [midpoint_blockEntryCubeMean_separation] at hzero
  norm_num at hzero

/-! ## Biology-facing names -/

/-- The order-`q` orientation-sensitive LD traffic invariant in the locus coordinate basis.

Empirical status: UNTESTED. A renaming of `entryPowerSum` in biological vocabulary, carrying
that definition's status: algebra, with no panel computation behind it. -/
noncomputable def ldOrientationInvariant {Locus : Type*} [Fintype Locus]
    (order : ℕ) (ld : Matrix Locus Locus ℝ) : ℝ :=
  entryPowerSum ld order

/-- **All-order architecture/LD contraction.**  An independent effect architecture with scalar
order-`q` cumulant detects LD orientation through the `q`-parallel-edge traffic invariant.
This contains both the skewed third-moment and symmetric fourth-cumulant mechanisms. -/
theorem independentArchitecture_cumulantEnergy_eq_ldOrientationInvariant
    {Row Locus : Type*} [Fintype Row] [Fintype Locus]
    (order : ℕ) (ldSquareRoot : Matrix Row Locus ℝ) (effectCumulant : ℝ) :
    cumulantTensorEnergy order
        (pushedCumulantTensor order ldSquareRoot effectCumulant) =
      effectCumulant ^ 2 *
        ldOrientationInvariant order (gramCovariance ldSquareRoot) := by
  exact cumulantTensorEnergy_pushedCumulantTensor order ldSquareRoot effectCumulant

/-- The orientation-sensitive third-order LD invariant in the locus coordinate basis.

Empirical status: UNTESTED, as for `ldOrientationInvariant`: algebra on the LD matrix, never
evaluated on a real one here. -/
noncomputable def ldOrientationThirdInvariant {Locus : Type*} [Fintype Locus]
    (ld : Matrix Locus Locus ℝ) : ℝ :=
  entryCubeSum ld

/-- A skewed independent effect architecture detects LD orientation through the general tensor
identity.  The theorem is an exact finite-locus statement, not an asymptotic analogy. -/
theorem skewedArchitecture_thirdMomentEnergy_eq_ldOrientationInvariant
    {Row Locus : Type*} [Fintype Row] [Fintype Locus]
    (ldSquareRoot : Matrix Row Locus ℝ) (effectThirdMoment : ℝ) :
    thirdTensorEnergy
        (pushedThirdMomentTensor ldSquareRoot effectThirdMoment) =
      effectThirdMoment ^ 2 *
        ldOrientationThirdInvariant (gramCovariance ldSquareRoot) := by
  exact thirdTensorEnergy_pushedThirdMomentTensor ldSquareRoot effectThirdMoment

/-- Gaussian or any symmetric effect architecture erases this particular obstruction because its
third moment is zero.  Higher even-order contractions may still retain orientation. -/
theorem symmetricArchitecture_thirdMomentEnergy_eq_zero
    {Row Locus : Type*} [Fintype Row] [Fintype Locus]
    (ldSquareRoot : Matrix Row Locus ℝ) :
    thirdTensorEnergy (pushedThirdMomentTensor ldSquareRoot 0) = 0 := by
  rw [thirdTensorEnergy_pushedThirdMomentTensor]
  simp

/-- The orientation-sensitive fourth-order LD invariant in the locus coordinate basis.  It is
the summed fourth-power LD score and remains visible for symmetric sparse effect priors.

Empirical status: UNTESTED. "Remains visible" is proved on the explicit witness pair below,
at one dimension and one prior; it is not a measurement on genotype data. -/
noncomputable def ldOrientationFourthInvariant {Locus : Type*} [Fintype Locus]
    (ld : Matrix Locus Locus ℝ) : ℝ :=
  entryFourthSum ld

/-- A symmetric non-Gaussian effect architecture detects LD orientation through its fourth
cumulant.  This is an exact finite-locus identity and covers the biologically standard case in
which reference-allele recoding forces the third moment to vanish. -/
theorem symmetricNonGaussianArchitecture_fourthCumulantEnergy_eq_ldOrientationInvariant
    {Row Locus : Type*} [Fintype Row] [Fintype Locus]
    (ldSquareRoot : Matrix Row Locus ℝ) (effectFourthCumulant : ℝ) :
    fourthTensorEnergy
        (pushedFourthCumulantTensor ldSquareRoot effectFourthCumulant) =
      effectFourthCumulant ^ 2 *
        ldOrientationFourthInvariant (gramCovariance ldSquareRoot) := by
  exact fourthTensorEnergy_pushedFourthCumulantTensor ldSquareRoot effectFourthCumulant

/-- The fourth-order LD invariant is directly estimable as a sum of per-variant fourth-power
LD scores, mirroring the standard squared-correlation LD score with exponent four. -/
theorem ldOrientationFourthInvariant_eq_sum_ldPowerScore_four
    {Locus : Type*} [Fintype Locus] (ld : Matrix Locus Locus ℝ) :
    ldOrientationFourthInvariant ld = ∑ j, ldPowerScore ld 4 j := by
  exact entryFourthSum_eq_sum_ldPowerScore_four ld

end Calibrator
