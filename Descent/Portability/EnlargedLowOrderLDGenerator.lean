/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.TwoLocusHistory

assert_below Descent.Decision Descent.Program

/-!
# The enlarged low-order feature family and its generator

NOTE1 equation (6) enlarges the stored two-locus moment family by the right-locus
heterozygosities `H^R_ij = q_i + q_j - 2 q_i q_j`, keeping all ordered indices.  The
enlargement is not cosmetic: the stored model identifies the *expected* left and right
heterozygosities, so silently setting `H^L = H^R` before applying the generator would be
invalid.  The corpus generator `augmentedLowOrderLDGenerator` carries no `H^R` row at all, and
its `pi2` mutation row reads the common expected heterozygosity off the stored `H` column.

This module builds the enlarged index set `AffineEnlargedCoordinate D`, its feature map
`enlargedLowOrderLDFeature`, and the enlarged generator `enlargedLowOrderLDGenerator`.  The
enlarged generator agrees with the corpus generator on every stored row except that the `pi2`
row's dependence on a right-locus heterozygosity, the coefficient
`(theta_first + theta_second) / 8` sitting on the stored `H(third, fourth)` column of
`lowOrderLDMutationCoupling`, is moved to the matching `H^R` column.  The `H^R` rows are the
corpus's own `H` rows read at right-locus indices, which is exactly NOTE1's observation that
both heterozygosity families obey the same affine one-locus system with the same forcing.

The embedding `embedLowOrderLDState` duplicates each stored `H` coordinate into the matching
`H^R` coordinate.  `enlargedGenerator_mulVec_embed` proves the intertwining `A~ E = E A` in
vector form, `enlargedGenerator_intertwines` restates it as a matrix identity, and
`enlargedPropagator_mulVec_embed` passes it through the exact matrix exponential using the
corpus's `matrixExponential_intertwines`.  This is the algebraic half of NOTE1 Theorem 2: the
subspace `E H^L_ij = E H^R_ij` of equation (12) is invariant, and on it the restriction to the
stored coordinates is exactly the corpus generator.

The realizability half is supplied in the two directions a caller needs.
`embed_eq_enlargedFeature_expectation` shows that every state carrying a
`LocusExchangeableLowOrderLDHaplotypeRealization` has its embedded vector equal to the
expectation of the enlarged feature map under the same haplotype law, and
`locusExchangeableRealizationOfEnlargedFeature` reads a locus-exchangeable realization back
out of such an expectation.  What is NOT proved here is the compactness and closedness of the
enlarged realization body, nor the microscopic-kernel expansion: those belong to the
realization-body and kernel packages, and the propagation statement itself to the
realizability-preservation module.

## Empirical status

None.  The bodies here are algebra: finite index bookkeeping, one matrix identity between
polynomial generator entries, and the definitional readout of a probability law's moments.
No measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EnlargedLowOrderLDGenerator

open Coalescent

noncomputable section

/-- The enlarged low-order index set of NOTE1 equation (6): the stored coordinates
`H`, `DD`, `Dz`, `pi2` together with one right-locus heterozygosity coordinate for every
ordered pair of demes. -/
abbrev EnlargedLowOrderLDCoordinate (D : ℕ) := LowOrderLDCoordinate D ⊕ (Fin D × Fin D)

/-- The enlarged index set with the constant coordinate adjoined, so that the mutation influx
travels inside the same matrix exponential. -/
abbrev AffineEnlargedCoordinate (D : ℕ) := Option (EnlargedLowOrderLDCoordinate D)

/-- The enlarged feature map: the constant one, the stored low-order polynomial coordinates
read from the haplotype state, and the cross-deme right-locus heterozygosity. -/
def enlargedLowOrderLDFeature {D : ℕ} (state : Fin D → TwoLocusHaplotypeFrequencies) :
    AffineEnlargedCoordinate D → ℝ
  | none => 1
  | some (.inl coordinate) => twoLocusJetMoment state coordinate
  | some (.inr pair) => twoLocusRightHeterozygosity (state pair.1) (state pair.2)

/-- The stored coordinate that an enlarged coordinate is a copy of: a right-locus
heterozygosity index is a copy of the matching stored `H` index. -/
def storedSource {D : ℕ} : AffineEnlargedCoordinate D → AffineLowOrderLDCoordinate D
  | none => none
  | some (.inl coordinate) => some coordinate
  | some (.inr pair) => some (.H pair.1 pair.2)

/-- Duplicate a stored low-order state into the enlarged index set, sending each stored `H`
coordinate to both the stored `H` and the matching `H^R` coordinate.  This is the embedding
`E` of NOTE1 Theorem 2. -/
def embedLowOrderLDState {D : ℕ} (state : AffineLowOrderLDCoordinate D → ℝ) :
    AffineEnlargedCoordinate D → ℝ := fun coordinate ↦ state (storedSource coordinate)

/-- The embedding as a rectangular matrix, so that it can be pushed through the exact matrix
exponential. -/
def enlargedEmbedding (D : ℕ) :
    Matrix (AffineEnlargedCoordinate D) (AffineLowOrderLDCoordinate D) ℝ :=
  fun row column ↦ if column = storedSource row then 1 else 0

/-- Coefficient with which a stored row reads an expected right-locus heterozygosity.  Only
the `pi2` row has one: its left-locus mutation channel contributes `H^R / 8` per unit of the
left-index mutation rate, which is the term `lowOrderLDMutationCoupling` places on the stored
`H(third, fourth)` column. -/
def rightHeterozygosityMutationCoupling {D : ℕ} (rates : ManyDemeLDRates D) :
    LowOrderLDCoordinate D → Fin D → Fin D → ℝ
  | .pi2 first second third fourth, leftIndex, rightIndex =>
      if third = leftIndex ∧ fourth = rightIndex then
        (rates.mutation first + rates.mutation second) / 8
      else 0
  | _, _, _ => 0

/-- The same coefficient read on a stored column: it is supported on the `H` columns only,
and there it agrees with the right-locus coupling.  Subtracting it from the corpus generator
is exactly the removal of the identification `H^L = H^R`. -/
def storedHeterozygosityMutationCoupling {D : ℕ} (rates : ManyDemeLDRates D)
    (row : LowOrderLDCoordinate D) : LowOrderLDCoordinate D → ℝ
  | .H first second => rightHeterozygosityMutationCoupling rates row first second
  | _ => 0

/-- The enlarged generator of NOTE1 section 2.2.  Stored rows are the corpus rows with the
`pi2` mutation row's right-locus heterozygosity dependence moved off the stored `H` column and
onto the matching `H^R` column; `H^R` rows are the corpus's `H` rows read at right-locus
indices; the constant row is zero. -/
def enlargedLowOrderLDGenerator {D : ℕ} (rates : ManyDemeLDRates D) :
    Matrix (AffineEnlargedCoordinate D) (AffineEnlargedCoordinate D) ℝ
  | none, _ => 0
  | some (.inl row), none => augmentedLowOrderLDGenerator rates (some row) none
  | some (.inl row), some (.inl column) =>
      augmentedLowOrderLDGenerator rates (some row) (some column) -
        storedHeterozygosityMutationCoupling rates row column
  | some (.inl row), some (.inr pair) =>
      rightHeterozygosityMutationCoupling rates row pair.1 pair.2
  | some (.inr pair), none => augmentedLowOrderLDGenerator rates (some (.H pair.1 pair.2)) none
  | some (.inr _), some (.inl _) => 0
  | some (.inr pair), some (.inr other) =>
      augmentedLowOrderLDGenerator rates (some (.H pair.1 pair.2))
        (some (.H other.1 other.2))

/-! ## Finite sum bookkeeping -/

/-- Matrix application written as the defining finite sum. -/
private theorem mulVec_apply_sum {index column : Type*} [Fintype column]
    (matrix : Matrix index column ℝ) (vector : column → ℝ) (row : index) :
    matrix.mulVec vector row = ∑ entry, matrix row entry * vector entry := rfl

/-- Applying a matrix to a one-hot vector reads off one entry. -/
private theorem mulVec_single_apply {index column : Type*} [Fintype column]
    [DecidableEq column] (matrix : Matrix index column ℝ) (target : column) (row : index) :
    matrix.mulVec (Pi.single target (1 : ℝ)) row = matrix row target := by
  classical
  rw [mulVec_apply_sum, Finset.sum_eq_single target]
  · rw [Pi.single_eq_same, mul_one]
  · intro other _ hother
    rw [Pi.single_eq_of_ne hother, mul_zero]
  · intro hmember
    exact absurd (Finset.mem_univ target) hmember

/-- A sum over the stored coordinates of a quantity supported on the heterozygosity
constructor collapses to a sum over ordered deme pairs. -/
private theorem sum_heterozygosity_columns {D : ℕ} (summand : LowOrderLDCoordinate D → ℝ)
    (hvanish : ∀ coordinate : LowOrderLDCoordinate D,
      (∀ first second : Fin D, coordinate ≠ .H first second) → summand coordinate = 0) :
    ∑ coordinate : LowOrderLDCoordinate D, summand coordinate =
      ∑ pair : Fin D × Fin D, summand (.H pair.1 pair.2) := by
  classical
  have himage : ∑ coordinate ∈ Finset.image
      (fun pair : Fin D × Fin D ↦ (LowOrderLDCoordinate.H pair.1 pair.2)) Finset.univ,
      summand coordinate = ∑ pair : Fin D × Fin D, summand (.H pair.1 pair.2) := by
    refine Finset.sum_image ?_
    intro firstPair _ secondPair _ hequal
    simpa [Prod.ext_iff] using hequal
  rw [← himage]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro coordinate _ hcoordinate
  refine hvanish coordinate ?_
  intro first second hequal
  exact hcoordinate (Finset.mem_image.mpr ⟨(first, second), Finset.mem_univ _, hequal.symm⟩)

/-- The stored `H` subsystem is closed: the corpus generator's `H` row has no entry on a
`DD`, `Dz`, or `pi2` column.  This is what licenses the enlarged `H^R` rows to read only
`H^R` columns. -/
theorem augmentedGenerator_heterozygosity_row_of_other {D : ℕ} (rates : ManyDemeLDRates D)
    (first second : Fin D) (column : LowOrderLDCoordinate D)
    (hcolumn : ∀ leftIndex rightIndex : Fin D, column ≠ .H leftIndex rightIndex) :
    augmentedLowOrderLDGenerator rates (some (.H first second)) (some column) = 0 := by
  classical
  rcases column with ⟨k, l⟩ | ⟨k, l⟩ | ⟨k, l, m⟩ | ⟨k, l, m, n⟩
  · exact absurd rfl (hcolumn k l)
  all_goals
    simp [augmentedLowOrderLDGenerator, lowOrderLDHomogeneousGenerator, lowOrderLDDrift,
      lowOrderLDMigration, lowOrderLDRecombination, lowOrderLDMutationCoupling,
      lowOrderLDRecurrentMutationDamping, lowOrderLDBasis]

/-! ## The embedding and the intertwining -/

/-- The embedding matrix implements the duplication of stored heterozygosities. -/
theorem enlargedEmbedding_mulVec {D : ℕ} (state : AffineLowOrderLDCoordinate D → ℝ) :
    (enlargedEmbedding D).mulVec state = embedLowOrderLDState state := by
  classical
  funext row
  rw [mulVec_apply_sum]
  simp only [enlargedEmbedding]
  rw [Finset.sum_eq_single (storedSource row)]
  · rw [if_pos rfl, one_mul]
    rfl
  · intro other _ hother
    rw [if_neg hother, zero_mul]
  · intro hmember
    exact absurd (Finset.mem_univ (storedSource row)) hmember

/-- Expansion of an enlarged matrix application into its constant, stored, and right-locus
heterozygosity blocks. -/
private theorem enlarged_mulVec_split {D : ℕ}
    (matrix : Matrix (AffineEnlargedCoordinate D) (AffineEnlargedCoordinate D) ℝ)
    (vector : AffineEnlargedCoordinate D → ℝ) (row : AffineEnlargedCoordinate D) :
    matrix.mulVec vector row = matrix row none * vector none +
      ((∑ coordinate : LowOrderLDCoordinate D,
          matrix row (some (.inl coordinate)) * vector (some (.inl coordinate))) +
        ∑ pair : Fin D × Fin D,
          matrix row (some (.inr pair)) * vector (some (.inr pair))) := by
  rw [mulVec_apply_sum, Fintype.sum_option, Fintype.sum_sum_type]

/-- Expansion of a stored matrix application into its constant and stored blocks. -/
private theorem affine_mulVec_split {D : ℕ}
    (matrix : Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ)
    (vector : AffineLowOrderLDCoordinate D → ℝ) (row : AffineLowOrderLDCoordinate D) :
    matrix.mulVec vector row = matrix row none * vector none +
      ∑ coordinate : LowOrderLDCoordinate D,
        matrix row (some coordinate) * vector (some coordinate) := by
  rw [mulVec_apply_sum, Fintype.sum_option]

/-- **The enlarged generator intertwines with the embedding.**  Applying the enlarged
generator to a duplicated state is the duplication of the corpus generator applied to the
stored state: the `pi2` row's right-locus heterozygosity dependence, moved to the `H^R`
column, reads exactly the value the stored `H` column carried, and the `H^R` rows reproduce
the closed `H` subsystem. -/
theorem enlargedGenerator_mulVec_embed {D : ℕ} (rates : ManyDemeLDRates D)
    (state : AffineLowOrderLDCoordinate D → ℝ) :
    (enlargedLowOrderLDGenerator rates).mulVec (embedLowOrderLDState state) =
      embedLowOrderLDState ((augmentedLowOrderLDGenerator rates).mulVec state) := by
  classical
  funext row
  rw [enlarged_mulVec_split]
  cases row with
  | none =>
      have hstored : embedLowOrderLDState
          ((augmentedLowOrderLDGenerator rates).mulVec state) none =
          (augmentedLowOrderLDGenerator rates).mulVec state none := rfl
      rw [hstored, affine_mulVec_split]
      simp [enlargedLowOrderLDGenerator, embedLowOrderLDState, augmentedLowOrderLDGenerator]
  | some enlarged =>
    cases enlarged with
    | inl storedRow =>
        have hstored : embedLowOrderLDState
            ((augmentedLowOrderLDGenerator rates).mulVec state) (some (.inl storedRow)) =
            (augmentedLowOrderLDGenerator rates).mulVec state (some storedRow) := rfl
        rw [hstored, affine_mulVec_split]
        have hcoupling : ∑ coordinate : LowOrderLDCoordinate D,
            storedHeterozygosityMutationCoupling rates storedRow coordinate *
              state (some coordinate) =
            ∑ pair : Fin D × Fin D,
              rightHeterozygosityMutationCoupling rates storedRow pair.1 pair.2 *
                state (some (.H pair.1 pair.2)) := by
          refine sum_heterozygosity_columns _ ?_
          intro coordinate hcoordinate
          rcases coordinate with ⟨k, l⟩ | ⟨k, l⟩ | ⟨k, l, m⟩ | ⟨k, l, m, n⟩
          · exact absurd rfl (hcoordinate k l)
          all_goals simp [storedHeterozygosityMutationCoupling]
        have hsplit : ∑ coordinate : LowOrderLDCoordinate D,
            (augmentedLowOrderLDGenerator rates (some storedRow) (some coordinate) -
                storedHeterozygosityMutationCoupling rates storedRow coordinate) *
              state (some coordinate) =
            (∑ coordinate : LowOrderLDCoordinate D,
              augmentedLowOrderLDGenerator rates (some storedRow) (some coordinate) *
                state (some coordinate)) -
            ∑ coordinate : LowOrderLDCoordinate D,
              storedHeterozygosityMutationCoupling rates storedRow coordinate *
                state (some coordinate) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun _ _ ↦ by ring
        simp only [enlargedLowOrderLDGenerator, embedLowOrderLDState, storedSource]
        rw [hsplit, hcoupling]
        ring
    | inr pair =>
        have hstored : embedLowOrderLDState
            ((augmentedLowOrderLDGenerator rates).mulVec state) (some (.inr pair)) =
            (augmentedLowOrderLDGenerator rates).mulVec state (some (.H pair.1 pair.2)) := rfl
        rw [hstored, affine_mulVec_split]
        have hclosed : ∑ coordinate : LowOrderLDCoordinate D,
            augmentedLowOrderLDGenerator rates (some (.H pair.1 pair.2)) (some coordinate) *
              state (some coordinate) =
            ∑ other : Fin D × Fin D,
              augmentedLowOrderLDGenerator rates (some (.H pair.1 pair.2))
                (some (.H other.1 other.2)) * state (some (.H other.1 other.2)) := by
          refine sum_heterozygosity_columns _ ?_
          intro coordinate hcoordinate
          rw [augmentedGenerator_heterozygosity_row_of_other rates pair.1 pair.2 coordinate
            hcoordinate, zero_mul]
        simp only [enlargedLowOrderLDGenerator, embedLowOrderLDState, storedSource]
        rw [hclosed]
        simp

/-- The intertwining as a matrix identity `E A = A~ E`. -/
theorem enlargedGenerator_intertwines {D : ℕ} (rates : ManyDemeLDRates D) :
    enlargedEmbedding D * augmentedLowOrderLDGenerator rates =
      enlargedLowOrderLDGenerator rates * enlargedEmbedding D := by
  classical
  apply Matrix.ext
  intro row column
  rw [← mulVec_single_apply (enlargedEmbedding D * augmentedLowOrderLDGenerator rates) column
      row,
    ← mulVec_single_apply (enlargedLowOrderLDGenerator rates * enlargedEmbedding D) column row,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, enlargedEmbedding_mulVec,
    enlargedEmbedding_mulVec, enlargedGenerator_mulVec_embed]

/-- **The enlarged epoch propagator intertwines with the embedding.**  Exponentiating the
enlarged generator and then reading the stored coordinates is the same as exponentiating the
corpus generator, which is NOTE1's statement that the locus-exchangeable subspace (12) is
invariant and the restriction there is exactly `augmentedLowOrderLDGenerator`. -/
theorem enlargedPropagator_mulVec_embed {D : ℕ} (rates : ManyDemeLDRates D) (duration : ℝ)
    (state : AffineLowOrderLDCoordinate D → ℝ) :
    (matrixExponential (enlargedLowOrderLDGenerator rates) duration).mulVec
        (embedLowOrderLDState state) =
      embedLowOrderLDState
        ((matrixExponential (augmentedLowOrderLDGenerator rates) duration).mulVec state) := by
  have hmatrix := matrixExponential_intertwines (enlargedEmbedding D)
    (augmentedLowOrderLDGenerator rates) (enlargedLowOrderLDGenerator rates)
    (enlargedGenerator_intertwines rates) duration
  rw [← enlargedEmbedding_mulVec, ← enlargedEmbedding_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hmatrix]

/-! ## Realizability of embedded states -/

/-- A locus-exchangeable haplotype realization of a stored state realizes its embedding as an
expectation of the enlarged feature map.  The `H^R` coordinate is where the extra field
`H_right_eq` is consumed. -/
theorem embed_eq_enlargedFeature_expectation {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state)
    (coordinate : AffineEnlargedCoordinate D) :
    embedLowOrderLDState state coordinate =
      realization.expectation (fun outcome ↦
        enlargedLowOrderLDFeature (realization.haplotype outcome) coordinate) := by
  cases coordinate with
  | none =>
      simp only [embedLowOrderLDState, storedSource, enlargedLowOrderLDFeature]
      rw [realization.constant_eq, realization.expectation.const_one]
  | some enlarged =>
    cases enlarged with
    | inl storedCoordinate =>
        cases storedCoordinate with
        | H first second =>
            simp only [embedLowOrderLDState, storedSource, enlargedLowOrderLDFeature,
              twoLocusJetMoment, twoLocusCoordinateJet, twoLocusHJet_value]
            exact realization.H_eq first second
        | DD first second =>
            simp only [embedLowOrderLDState, storedSource, enlargedLowOrderLDFeature,
              twoLocusJetMoment, twoLocusCoordinateJet, twoLocusDDJet_value]
            exact realization.DD_eq first second
        | Dz first second third =>
            simp only [embedLowOrderLDState, storedSource, enlargedLowOrderLDFeature,
              twoLocusJetMoment, twoLocusCoordinateJet, twoLocusDzJet_value]
            exact realization.Dz_eq first second third
        | pi2 first second third fourth =>
            simp only [embedLowOrderLDState, storedSource, enlargedLowOrderLDFeature,
              twoLocusJetMoment, twoLocusCoordinateJet, twoLocusPi2Jet_value]
            exact realization.pi2_eq first second third fourth
    | inr pair =>
        simp only [embedLowOrderLDState, storedSource, enlargedLowOrderLDFeature]
        exact realization.H_right_eq pair.1 pair.2

/-- A haplotype law whose enlarged feature expectations reproduce an embedded stored state
supplies the locus-exchangeable realization of that state.  This is the converse direction of
NOTE1 Theorem 2 and the concrete inhabitant of the locus-exchangeable structure used by the
propagation argument.

Assumes: `hfeature` holds at every enlarged coordinate, so in particular at both the stored
`H` index and its right-locus copy. -/
def locusExchangeableRealizationOfEnlargedFeature {D : ℕ} {sampleSpace : Type}
    (expectation : Foundations.ExpFunctional sampleSpace)
    (haplotype : sampleSpace → Fin D → TwoLocusHaplotypeFrequencies)
    (state : AffineLowOrderLDCoordinate D → ℝ)
    (hfeature : ∀ coordinate : AffineEnlargedCoordinate D,
      embedLowOrderLDState state coordinate =
        expectation (fun outcome ↦
          enlargedLowOrderLDFeature (haplotype outcome) coordinate)) :
    LocusExchangeableLowOrderLDHaplotypeRealization state where
  sampleSpace := sampleSpace
  expectation := expectation
  haplotype := haplotype
  constant_eq := by
    have hnone := hfeature none
    simp only [embedLowOrderLDState, storedSource, enlargedLowOrderLDFeature] at hnone
    rw [hnone, expectation.const_one]
  H_eq first second := by
    have hentry := hfeature (some (.inl (.H first second)))
    simpa only [embedLowOrderLDState, storedSource, enlargedLowOrderLDFeature,
      twoLocusJetMoment, twoLocusCoordinateJet, twoLocusHJet_value] using hentry
  DD_eq first second := by
    have hentry := hfeature (some (.inl (.DD first second)))
    simpa only [embedLowOrderLDState, storedSource, enlargedLowOrderLDFeature,
      twoLocusJetMoment, twoLocusCoordinateJet, twoLocusDDJet_value] using hentry
  Dz_eq first second third := by
    have hentry := hfeature (some (.inl (.Dz first second third)))
    simpa only [embedLowOrderLDState, storedSource, enlargedLowOrderLDFeature,
      twoLocusJetMoment, twoLocusCoordinateJet, twoLocusDzJet_value] using hentry
  pi2_eq first second third fourth := by
    have hentry := hfeature (some (.inl (.pi2 first second third fourth)))
    simpa only [embedLowOrderLDState, storedSource, enlargedLowOrderLDFeature,
      twoLocusJetMoment, twoLocusCoordinateJet, twoLocusPi2Jet_value] using hentry
  H_right_eq first second := by
    have hentry := hfeature (some (.inr (first, second)))
    simpa only [embedLowOrderLDState, storedSource, enlargedLowOrderLDFeature] using hentry

/-! ## Matrix application in generator-row form -/

/-- The drift row is additive in the moment vector. -/
private theorem drift_add {D : ℕ} (rates : ManyDemeLDRates D)
    (first second : LowOrderLDCoordinate D → ℝ) (row : LowOrderLDCoordinate D) :
    lowOrderLDDrift rates (first + second) row =
      lowOrderLDDrift rates first row + lowOrderLDDrift rates second row := by
  cases row <;> simp only [lowOrderLDDrift, Pi.add_apply] <;> split_ifs <;> ring

/-- The drift row is homogeneous in the moment vector. -/
private theorem drift_smul {D : ℕ} (rates : ManyDemeLDRates D) (scalar : ℝ)
    (moment : LowOrderLDCoordinate D → ℝ) (row : LowOrderLDCoordinate D) :
    lowOrderLDDrift rates (scalar • moment) row =
      scalar * lowOrderLDDrift rates moment row := by
  cases row <;> simp only [lowOrderLDDrift, Pi.smul_apply, smul_eq_mul] <;>
    split_ifs <;> ring

/-- The migration row is additive in the moment vector. -/
private theorem migration_add {D : ℕ} (rates : ManyDemeLDRates D)
    (first second : LowOrderLDCoordinate D → ℝ) (row : LowOrderLDCoordinate D) :
    lowOrderLDMigration rates (first + second) row =
      lowOrderLDMigration rates first row + lowOrderLDMigration rates second row := by
  cases row <;>
    simp only [lowOrderLDMigration, Pi.add_apply, mul_add, mul_sub, add_div, sub_div,
      mul_div_assoc, Finset.sum_add_distrib, Finset.sum_sub_distrib] <;> ring

/-- The migration row is homogeneous in the moment vector. -/
private theorem migration_smul {D : ℕ} (rates : ManyDemeLDRates D) (scalar : ℝ)
    (moment : LowOrderLDCoordinate D → ℝ) (row : LowOrderLDCoordinate D) :
    lowOrderLDMigration rates (scalar • moment) row =
      scalar * lowOrderLDMigration rates moment row := by
  cases row <;>
    simp only [lowOrderLDMigration, Pi.smul_apply, smul_eq_mul, mul_add, mul_sub, add_div,
      sub_div, mul_div_assoc, Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, mul_comm, mul_left_comm, mul_assoc] <;> ring

/-- The recombination row is additive in the moment vector. -/
private theorem recombination_add {D : ℕ} (rates : ManyDemeLDRates D)
    (first second : LowOrderLDCoordinate D → ℝ) (row : LowOrderLDCoordinate D) :
    lowOrderLDRecombination rates (first + second) row =
      lowOrderLDRecombination rates first row + lowOrderLDRecombination rates second row := by
  cases row <;> simp only [lowOrderLDRecombination, Pi.add_apply] <;> ring

/-- The recombination row is homogeneous in the moment vector. -/
private theorem recombination_smul {D : ℕ} (rates : ManyDemeLDRates D) (scalar : ℝ)
    (moment : LowOrderLDCoordinate D → ℝ) (row : LowOrderLDCoordinate D) :
    lowOrderLDRecombination rates (scalar • moment) row =
      scalar * lowOrderLDRecombination rates moment row := by
  cases row <;> simp only [lowOrderLDRecombination, Pi.smul_apply, smul_eq_mul] <;> ring

/-- The mutation coupling row is additive in the moment vector. -/
private theorem coupling_add {D : ℕ} (rates : ManyDemeLDRates D)
    (first second : LowOrderLDCoordinate D → ℝ) (row : LowOrderLDCoordinate D) :
    lowOrderLDMutationCoupling rates (first + second) row =
      lowOrderLDMutationCoupling rates first row +
        lowOrderLDMutationCoupling rates second row := by
  cases row <;> simp only [lowOrderLDMutationCoupling, Pi.add_apply] <;> ring

/-- The mutation coupling row is homogeneous in the moment vector. -/
private theorem coupling_smul {D : ℕ} (rates : ManyDemeLDRates D) (scalar : ℝ)
    (moment : LowOrderLDCoordinate D → ℝ) (row : LowOrderLDCoordinate D) :
    lowOrderLDMutationCoupling rates (scalar • moment) row =
      scalar * lowOrderLDMutationCoupling rates moment row := by
  cases row <;> simp only [lowOrderLDMutationCoupling, Pi.smul_apply, smul_eq_mul] <;> ring

/-- The recurrent mutation damping row is additive in the moment vector. -/
private theorem damping_add {D : ℕ} (rates : ManyDemeLDRates D)
    (first second : LowOrderLDCoordinate D → ℝ) (row : LowOrderLDCoordinate D) :
    lowOrderLDRecurrentMutationDamping rates (first + second) row =
      lowOrderLDRecurrentMutationDamping rates first row +
        lowOrderLDRecurrentMutationDamping rates second row := by
  cases row <;> simp only [lowOrderLDRecurrentMutationDamping, Pi.add_apply] <;> ring

/-- The recurrent mutation damping row is homogeneous in the moment vector. -/
private theorem damping_smul {D : ℕ} (rates : ManyDemeLDRates D) (scalar : ℝ)
    (moment : LowOrderLDCoordinate D → ℝ) (row : LowOrderLDCoordinate D) :
    lowOrderLDRecurrentMutationDamping rates (scalar • moment) row =
      scalar * lowOrderLDRecurrentMutationDamping rates moment row := by
  cases row <;>
    simp only [lowOrderLDRecurrentMutationDamping, Pi.smul_apply, smul_eq_mul] <;> ring

/-- The homogeneous low-order generator as a linear map of the moment vector.  Linearity is
what lets the corpus's basis-column matrix be applied to a whole moment vector. -/
def lowOrderLDGeneratorMap {D : ℕ} (rates : ManyDemeLDRates D) :
    (LowOrderLDCoordinate D → ℝ) →ₗ[ℝ] (LowOrderLDCoordinate D → ℝ) where
  toFun := lowOrderLDHomogeneousGenerator rates
  map_add' first second := by
    funext row
    simp only [lowOrderLDHomogeneousGenerator, Pi.add_apply]
    rw [drift_add, migration_add, recombination_add, coupling_add, damping_add]
    ring
  map_smul' scalar moment := by
    funext row
    simp only [lowOrderLDHomogeneousGenerator, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [drift_smul, migration_smul, recombination_smul, coupling_smul, damping_smul]
    ring

/-- The linear map is the corpus generator. -/
theorem lowOrderLDGeneratorMap_apply {D : ℕ} (rates : ManyDemeLDRates D)
    (moment : LowOrderLDCoordinate D → ℝ) :
    lowOrderLDGeneratorMap rates moment = lowOrderLDHomogeneousGenerator rates moment := rfl

/-- Every moment vector is the basis expansion of its own coordinates. -/
theorem moment_eq_sum_basis {D : ℕ} (moment : LowOrderLDCoordinate D → ℝ) :
    moment = ∑ column : LowOrderLDCoordinate D, moment column • lowOrderLDBasis column := by
  classical
  funext coordinate
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, lowOrderLDBasis]
  rw [Finset.sum_eq_single coordinate]
  · rw [if_pos rfl, mul_one]
  · intro other _ hother
    rw [if_neg (Ne.symm hother), mul_zero]
  · intro hmember
    exact absurd (Finset.mem_univ coordinate) hmember

/-- The corpus generator applied to a moment vector is the basis-column expansion that the
augmented matrix stores. -/
theorem homogeneousGenerator_sum_basis {D : ℕ} (rates : ManyDemeLDRates D)
    (moment : LowOrderLDCoordinate D → ℝ) (row : LowOrderLDCoordinate D) :
    ∑ column : LowOrderLDCoordinate D,
        lowOrderLDHomogeneousGenerator rates (lowOrderLDBasis column) row * moment column =
      lowOrderLDHomogeneousGenerator rates moment row := by
  have hmap : lowOrderLDGeneratorMap rates moment =
      ∑ column : LowOrderLDCoordinate D,
        moment column • lowOrderLDGeneratorMap rates (lowOrderLDBasis column) := by
    conv_lhs => rw [moment_eq_sum_basis moment]
    rw [map_sum]
    exact Finset.sum_congr rfl fun column _ ↦ map_smul _ _ _
  have happly := congrFun hmap row
  rw [Finset.sum_apply] at happly
  simp only [Pi.smul_apply, smul_eq_mul, lowOrderLDGeneratorMap_apply] at happly
  rw [happly]
  exact Finset.sum_congr rfl fun column _ ↦ by ring

/-- **Matrix application of the corpus generator is its generator row.**  The constant column
carries the mutation forcing and the stored columns carry the homogeneous rows. -/
theorem augmentedGenerator_mulVec {D : ℕ} (rates : ManyDemeLDRates D)
    (state : AffineLowOrderLDCoordinate D → ℝ) (row : LowOrderLDCoordinate D) :
    (augmentedLowOrderLDGenerator rates).mulVec state (some row) =
      lowOrderLDHomogeneousGenerator rates (fun coordinate ↦ state (some coordinate)) row +
        lowOrderLDMutationForcing rates row * state none := by
  rw [affine_mulVec_split]
  have hentry : ∀ coordinate : LowOrderLDCoordinate D,
      augmentedLowOrderLDGenerator rates (some row) (some coordinate) =
        lowOrderLDHomogeneousGenerator rates (lowOrderLDBasis coordinate) row :=
    fun _ ↦ rfl
  have hconstant : augmentedLowOrderLDGenerator rates (some row) none =
      lowOrderLDMutationForcing rates row := rfl
  simp only [hentry, hconstant]
  rw [homogeneousGenerator_sum_basis]
  ring

/-- The right-locus heterozygosity block of an enlarged vector, read as a stored moment
vector supported on the `H` coordinates. -/
def rightHeterozygosityMoment {D : ℕ} (vector : AffineEnlargedCoordinate D → ℝ) :
    LowOrderLDCoordinate D → ℝ
  | .H first second => vector (some (.inr (first, second)))
  | _ => 0

/-- **The enlarged generator on a stored row.**  It is the corpus row of the stored block
plus the mutation forcing, corrected by the amount the `pi2` mutation channel now reads off
the right-locus heterozygosity instead of the stored one. -/
theorem enlargedGenerator_mulVec_stored {D : ℕ} (rates : ManyDemeLDRates D)
    (vector : AffineEnlargedCoordinate D → ℝ) (row : LowOrderLDCoordinate D) :
    (enlargedLowOrderLDGenerator rates).mulVec vector (some (.inl row)) =
      lowOrderLDHomogeneousGenerator rates
          (fun coordinate ↦ vector (some (.inl coordinate))) row +
        lowOrderLDMutationForcing rates row * vector none +
        ∑ pair : Fin D × Fin D,
          rightHeterozygosityMutationCoupling rates row pair.1 pair.2 *
            (vector (some (.inr pair)) -
              vector (some (.inl (.H pair.1 pair.2)))) := by
  classical
  rw [enlarged_mulVec_split]
  have hentry : ∀ coordinate : LowOrderLDCoordinate D,
      enlargedLowOrderLDGenerator rates (some (.inl row)) (some (.inl coordinate)) =
        lowOrderLDHomogeneousGenerator rates (lowOrderLDBasis coordinate) row -
          storedHeterozygosityMutationCoupling rates row coordinate := fun _ ↦ rfl
  have hconstant : enlargedLowOrderLDGenerator rates (some (.inl row)) none =
      lowOrderLDMutationForcing rates row := rfl
  have hpair : ∀ pair : Fin D × Fin D,
      enlargedLowOrderLDGenerator rates (some (.inl row)) (some (.inr pair)) =
        rightHeterozygosityMutationCoupling rates row pair.1 pair.2 := fun _ ↦ rfl
  have hcoupling : ∑ coordinate : LowOrderLDCoordinate D,
      storedHeterozygosityMutationCoupling rates row coordinate *
        vector (some (.inl coordinate)) =
      ∑ pair : Fin D × Fin D,
        rightHeterozygosityMutationCoupling rates row pair.1 pair.2 *
          vector (some (.inl (.H pair.1 pair.2))) := by
    refine sum_heterozygosity_columns
      (fun coordinate ↦ storedHeterozygosityMutationCoupling rates row coordinate *
        vector (some (.inl coordinate))) ?_
    intro coordinate hcoordinate
    rcases coordinate with ⟨k, l⟩ | ⟨k, l⟩ | ⟨k, l, m⟩ | ⟨k, l, m, n⟩
    · exact absurd rfl (hcoordinate k l)
    all_goals simp [storedHeterozygosityMutationCoupling]
  have hsplit : ∑ coordinate : LowOrderLDCoordinate D,
      (lowOrderLDHomogeneousGenerator rates (lowOrderLDBasis coordinate) row -
          storedHeterozygosityMutationCoupling rates row coordinate) *
        vector (some (.inl coordinate)) =
      (∑ coordinate : LowOrderLDCoordinate D,
        lowOrderLDHomogeneousGenerator rates (lowOrderLDBasis coordinate) row *
          vector (some (.inl coordinate))) -
      ∑ coordinate : LowOrderLDCoordinate D,
        storedHeterozygosityMutationCoupling rates row coordinate *
          vector (some (.inl coordinate)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  have hdifference : ∑ pair : Fin D × Fin D,
      rightHeterozygosityMutationCoupling rates row pair.1 pair.2 *
        (vector (some (.inr pair)) - vector (some (.inl (.H pair.1 pair.2)))) =
      (∑ pair : Fin D × Fin D,
        rightHeterozygosityMutationCoupling rates row pair.1 pair.2 *
          vector (some (.inr pair))) -
      ∑ pair : Fin D × Fin D,
        rightHeterozygosityMutationCoupling rates row pair.1 pair.2 *
          vector (some (.inl (.H pair.1 pair.2))) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  simp only [hentry, hconstant, hpair]
  rw [hsplit, hcoupling, hdifference, homogeneousGenerator_sum_basis]
  ring

/-- **The enlarged generator on a right-locus heterozygosity row.**  It is the corpus `H` row
read at the right-locus block, with the same affine mutation forcing: both heterozygosity
families obey the same one-locus system, which is the invariance statement of NOTE1 (12). -/
theorem enlargedGenerator_mulVec_rightHeterozygosity {D : ℕ} (rates : ManyDemeLDRates D)
    (vector : AffineEnlargedCoordinate D → ℝ) (first second : Fin D) :
    (enlargedLowOrderLDGenerator rates).mulVec vector (some (.inr (first, second))) =
      lowOrderLDHomogeneousGenerator rates (rightHeterozygosityMoment vector)
          (.H first second) +
        lowOrderLDMutationForcing rates (.H first second) * vector none := by
  classical
  rw [enlarged_mulVec_split]
  have hentry : ∀ pair : Fin D × Fin D,
      enlargedLowOrderLDGenerator rates (some (.inr (first, second))) (some (.inr pair)) =
        augmentedLowOrderLDGenerator rates (some (.H first second))
          (some (.H pair.1 pair.2)) := fun _ ↦ rfl
  have hstored : ∀ coordinate : LowOrderLDCoordinate D,
      enlargedLowOrderLDGenerator rates (some (.inr (first, second)))
        (some (.inl coordinate)) = 0 := fun _ ↦ rfl
  have hconstant : enlargedLowOrderLDGenerator rates (some (.inr (first, second))) none =
      lowOrderLDMutationForcing rates (.H first second) := rfl
  have hclosed : ∑ coordinate : LowOrderLDCoordinate D,
      lowOrderLDHomogeneousGenerator rates (lowOrderLDBasis coordinate) (.H first second) *
        rightHeterozygosityMoment vector coordinate =
      ∑ pair : Fin D × Fin D,
        augmentedLowOrderLDGenerator rates (some (.H first second))
            (some (.H pair.1 pair.2)) * vector (some (.inr pair)) := by
    refine sum_heterozygosity_columns _ ?_
    intro coordinate hcoordinate
    have hzero := augmentedGenerator_heterozygosity_row_of_other rates first second
      coordinate hcoordinate
    have hrow : lowOrderLDHomogeneousGenerator rates (lowOrderLDBasis coordinate)
        (.H first second) = 0 := hzero
    rw [hrow, zero_mul]
  simp only [hentry, hstored, hconstant, zero_mul, Finset.sum_const_zero]
  rw [← hclosed, homogeneousGenerator_sum_basis]
  ring

/-- The enlarged feature map of an actual haplotype configuration is realized by the Dirac
expectation at that configuration, so the enlarged family is inhabited by genuine laws rather
than merely constrained by equations. -/
theorem enlargedFeature_eq_diracExpectation {D : ℕ}
    (state : Fin D → TwoLocusHaplotypeFrequencies) (coordinate : AffineEnlargedCoordinate D) :
    enlargedLowOrderLDFeature state coordinate =
      (Foundations.ExpFunctional.evalAt state) (fun outcome ↦
        enlargedLowOrderLDFeature outcome coordinate) := rfl

end

end Descent.Portability.EnlargedLowOrderLDGenerator
