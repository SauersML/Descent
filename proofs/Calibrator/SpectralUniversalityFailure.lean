/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Calibrator

/-!
# Failure of spectral sufficiency for skewed product priors

This file formalizes the algebraic certificate behind the negative answer to Question S.
There are two rigid bases: the eigenbasis of a covariance matrix and the coordinate basis in
which a non-Gaussian prior factorizes.  A spectrum forgets their relative orientation.

The main result is dimension-general.  If independent centered coordinates have common third
moment `kappa` and are mixed by a matrix `L`, the squared Frobenius norm of the resulting third
moment tensor is

`kappa ^ 2 * sum i, sum j, ((L.transpose * L) i j) ^ 3`.

Thus the first orientation-sensitive contraction is the entrywise cube sum of the Gram matrix.
The second part gives an exact two-dimensional witness: a diagonal block and its forty-five
degree rotation have the same characteristic polynomial at every parameter value, but different
entrywise-cube invariants.  At the midpoint parameter their difference is exactly `11 / 8`, and
the corresponding low-SNR third coefficient differs by `11 / 24` for the sparse centered prior
with variance and third moment both equal to `2`.

No free-entropy limit theorem is assumed as a parameter here.  The declarations below prove the
finite-dimensional invariant and the coefficient separation on which such a theorem must act.
They therefore isolate the genuinely new mathematical obstruction without laundering the
adaptive-interpolation step.

## Biological interpretation

Take `L` to be a square root of a linkage-disequilibrium covariance matrix.  The input coordinates
are locus effects in the reference-allele basis.  For a skewed sparse architecture, `kappa` is
nonzero, so two populations can have identical LD eigenvalues and nevertheless have different
third-order denoising information.  The spectrum measures LD strength; the entrywise cube sum
also measures how LD eigenvectors are oriented relative to loci.  This is the basis information
that a spectral portability summary discards.
-/

open scoped BigOperators Matrix

section ThirdMomentContraction

variable {Row Locus : Type*} [Fintype Row] [Fintype Locus]

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
  simp only [pow_two, pow_three]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  ring_nf
  simp_rw [Fintype.sum_mul_sum]
  ring_nf

end ThirdMomentContraction

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

/-- The localized and rotated blocks are exactly isospectral for every value of `a`. -/
theorem localizedCovarianceBlock_isospectral_rotatedCovarianceBlock (a : ℝ) :
    Isospectral2 (localizedCovarianceBlock a) (rotatedCovarianceBlock a) := by
  intro spectralParameter
  simp [localizedCovarianceBlock, rotatedCovarianceBlock, Matrix.det_fin_two]
  ring

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

/-! ## The low-SNR coefficient and the Question S certificate -/

/-- The cubic low-SNR coefficient after the spectral terms and the orientation term are
separated.  `m1`, `m2`, and `m3` are spectral moments; `h3` is the entrywise-cube invariant. -/
noncomputable def lowSNRThirdCoefficient
    (aspect variance thirdMoment m1 m2 m3 h3 : ℝ) : ℝ :=
  variance ^ 3 / 6 *
      (m3 + 3 * m1 * m2 / aspect + m1 ^ 3 / aspect ^ 2) -
    thirdMoment ^ 2 / 12 * h3

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

/-- The orientation-sensitive third-order LD invariant in the locus coordinate basis. -/
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

end Calibrator
