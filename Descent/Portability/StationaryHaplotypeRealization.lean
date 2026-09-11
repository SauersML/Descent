/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EnlargedBodyClosedness
import Descent.Portability.StationaryRealization
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Exponential

assert_below Descent.Decision Descent.Program

/-!
# The ancestral stationary state has a common haplotype realization

This module proves NOTE1 Theorem 3 for the corpus closed form: the one-deme stationary
low-order state `oneDemeStationaryLowOrderLDState rates` of NOTE1 (16) carries a
locus-exchangeable haplotype realization, one common probability law on the haplotype simplex
whose moments are all of its coordinates, with the expected left- and right-locus
heterozygosities equal. `StationaryRealization` proved the Cesàro step and the determinant
identity (15) but left the orbit as a hypothesis; the orbit is constructed here.

The argument is the one of NOTE1 §3. Start from `abHaplotypeState`, the state in which every
chromosome carries the `AB` haplotype, whose stored feature vector embeds into the enlarged
family of NOTE1 (6) exactly because both loci are monomorphic
(`embed_lowOrderLDFeature_abHaplotypeState`). Propagate it with the exact one-deme semigroup.
`hasDerivAt_matrixExponential_mulVec` differentiates the orbit through Mathlib's
`hasDerivAt_exp_smul_const'`, and `augmentedGenerator_mulVec_oneDeme` reads the corpus
generator applied to a vector as `B w + b` of NOTE1 (14), using the corpus row identifications
`augmentedGenerator_eq_stationaryMatrix` and `augmentedGenerator_none_eq_stationaryForcing`
together with the bijection `oneDemeCoordinateEquiv` between the coordinate list of (14) and
the corpus coordinate type at one deme. So `hasDerivAt_oneDemeOrbit`: the four coordinates of
the orbit solve (14) at every time.

The set the orbit stays in is `oneDemeRealizableSet`, the vectors of (14) whose
locus-exchangeable embedding lies in the enlarged one-deme realization body. It is convex, it
is closed because the enlarged body is closed (`EnlargedBodyClosedness`), and it is bounded
because that body is compact. `oneDemeOrbit_mem_oneDemeRealizableSet` places the orbit in it
at every nonnegative time: the enlarged propagator intertwines with the embedding
(`enlargedPropagator_mulVec_embed`) and carries the enlarged body into itself whenever the
enlarged generator has a microscopic approximation (NOTE1 Theorem 1). The Cesàro lemma
`oneDemeStationaryVector_mem_of_orbit_mem` then puts the unique stationary vector in the set,
which is `embed_oneDemeStationaryLowOrderLDState_mem_of_approx`, and a point of the enlarged
body whose heterozygosity coordinates agree carries a locus-exchangeable realization,
`nonempty_stationaryLocusExchangeableRealization_of_approx`.

What is NOT proved here: the microscopic approximation of the enlarged one-deme generator,
NOTE1 (11). The theorems take it as data and are exactly as strong as the approximation they
are given; the hypothesis-free statement is its specialisation to the constructed kernel.

## Empirical status

None. The bodies here are algebra and analysis: a matrix-exponential orbit, a time average and
a convex hull of polynomial coordinates. No measurement can bear on whether a vector lies in a
convex hull.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.StationaryHaplotypeRealization

open Descent.Coalescent
open Descent.Portability.FiniteMixtureKernel
open Descent.Portability.RealizationBody
open Descent.Portability.StationaryRealization
open Descent.Portability.EnlargedLowOrderLDGenerator
  (AffineEnlargedCoordinate enlargedLowOrderLDGenerator embedLowOrderLDState
    enlargedPropagator_mulVec_embed)

noncomputable section

/-! ## The coordinates of NOTE1 (14) -/

/-- The coordinate list `(H, DD, Dz, pi2)` of NOTE1 (14) is a bijection onto the corpus
low-order coordinate type at one deme: with a single deme every index is `0`, so each of the
four constructors contributes exactly one coordinate. -/
def oneDemeCoordinateEquiv : Fin 4 ≃ LowOrderLDCoordinate 1 where
  toFun := oneDemeCoordinate
  invFun coordinate :=
    match coordinate with
    | .H _ _ => 0
    | .DD _ _ => 1
    | .Dz _ _ _ => 2
    | .pi2 _ _ _ _ => 3
  left_inv row := by
    fin_cases row <;> rfl
  right_inv coordinate := by
    have hzero : ∀ deme : Fin 1, deme = 0 := fun deme ↦ Subsingleton.elim deme 0
    cases coordinate with
    | H first second =>
      obtain rfl := hzero first
      obtain rfl := hzero second
      rfl
    | DD first second =>
      obtain rfl := hzero first
      obtain rfl := hzero second
      rfl
    | Dz first second third =>
      obtain rfl := hzero first
      obtain rfl := hzero second
      obtain rfl := hzero third
      rfl
    | pi2 first second third fourth =>
      obtain rfl := hzero first
      obtain rfl := hzero second
      obtain rfl := hzero third
      obtain rfl := hzero fourth
      rfl

/-- The bijection sends a row of NOTE1 (14) to its corpus coordinate. -/
@[simp] theorem oneDemeCoordinateEquiv_apply (row : Fin 4) :
    oneDemeCoordinateEquiv row = oneDemeCoordinate row := rfl

/-- The coordinates `(H, DD, Dz, pi2)` of NOTE1 (14) read off a one-deme low-order vector. -/
def oneDemeProjection (state : AffineLowOrderLDCoordinate 1 → ℝ) : Fin 4 → ℝ :=
  fun row ↦ state (some (oneDemeCoordinate row))

/-- The one-deme low-order vector whose affine coordinate is one and whose coordinates
`(H, DD, Dz, pi2)` are those of a vector of NOTE1 (14). -/
def oneDemeLift (vector : Fin 4 → ℝ) : AffineLowOrderLDCoordinate 1 → ℝ
  | none => 1
  | some stored => vector (oneDemeCoordinateEquiv.symm stored)

/-- Lifting the projection of a one-deme vector whose affine coordinate is one returns the
vector. -/
theorem oneDemeLift_oneDemeProjection (state : AffineLowOrderLDCoordinate 1 → ℝ)
    (hnone : state none = 1) : oneDemeLift (oneDemeProjection state) = state := by
  funext coordinate
  cases coordinate with
  | none => exact hnone.symm
  | some stored =>
    show state (some (oneDemeCoordinateEquiv (oneDemeCoordinateEquiv.symm stored)))
      = state (some stored)
    rw [Equiv.apply_symm_apply]

/-- **The corpus one-deme generator applied to a vector is the affine system of NOTE1 (14).**
The `(H, DD, Dz, pi2)` rows of the augmented generator applied to a one-deme low-order vector
are the matrix `B` applied to the four coordinates plus the forcing `b` times the affine
coordinate. -/
theorem augmentedGenerator_mulVec_oneDeme (rates : ManyDemeLDRates 1)
    (state : AffineLowOrderLDCoordinate 1 → ℝ) (row : Fin 4) :
    (augmentedLowOrderLDGenerator rates).mulVec state (some (oneDemeCoordinate row))
      = (oneDemeStationaryMatrix rates).mulVec (oneDemeProjection state) row
        + stationaryForcing (rates.mutation 0) row * state none := by
  have hexpand :
      (augmentedLowOrderLDGenerator rates).mulVec state (some (oneDemeCoordinate row))
        = ∑ column : AffineLowOrderLDCoordinate 1,
            augmentedLowOrderLDGenerator rates (some (oneDemeCoordinate row)) column
              * state column := rfl
  rw [hexpand, Fintype.sum_option, ← oneDemeCoordinateEquiv.sum_comp,
    augmentedGenerator_none_eq_stationaryForcing]
  simp only [oneDemeCoordinateEquiv_apply, augmentedGenerator_eq_stationaryMatrix]
  exact add_comm _ _

/-! ## The orbit solves the affine system -/

section Orbit

open scoped Matrix.Norms.Operator

/-- The orbit of a vector under the exact matrix exponential is differentiable at every time,
with derivative the generator applied to the orbit. -/
theorem hasDerivAt_matrixExponential_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (initial : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun time ↦ (matrixExponential A time).mulVec initial)
      (A.mulVec ((matrixExponential A t).mulVec initial)) t := by
  have hexp : HasDerivAt (fun time : ℝ ↦ NormedSpace.exp ℝ (time • A))
      (A * NormedSpace.exp ℝ (t • A)) t :=
    hasDerivAt_exp_smul_const' A t
  have hlinear := (LinearMap.toContinuousLinearMap
    (EulerInvariantSet.mulVecMap initial)).hasFDerivAt.comp_hasDerivAt t hexp
  have hfun : (fun time ↦ (matrixExponential A time).mulVec initial)
      = (LinearMap.toContinuousLinearMap (EulerInvariantSet.mulVecMap initial)) ∘
          fun time : ℝ ↦ NormedSpace.exp ℝ (time • A) := by
    funext time
    rw [matrixExponential_eq_normedSpace_exp]
    rfl
  rw [hfun, matrixExponential_eq_normedSpace_exp, Matrix.mulVec_mulVec]
  exact hlinear

end Orbit

/-- **The one-deme orbit solves NOTE1 (14).** The coordinates `(H, DD, Dz, pi2)` of the exact
one-deme orbit started from a vector with affine coordinate one satisfy `w' = B w + b` at every
time. The affine coordinate stays one because the constant row of the corpus generator is
zero. -/
theorem hasDerivAt_oneDemeOrbit (rates : ManyDemeLDRates 1)
    (initial : AffineLowOrderLDCoordinate 1 → ℝ) (hinitial : initial none = 1) (t : ℝ) :
    HasDerivAt (fun time ↦ oneDemeProjection
        ((matrixExponential (augmentedLowOrderLDGenerator rates) time).mulVec initial))
      ((oneDemeStationaryMatrix rates).mulVec (oneDemeProjection
          ((matrixExponential (augmentedLowOrderLDGenerator rates) t).mulVec initial))
        + stationaryForcing (rates.mutation 0)) t := by
  have horbit :=
    hasDerivAt_matrixExponential_mulVec (augmentedLowOrderLDGenerator rates) initial t
  have hnone :
      (matrixExponential (augmentedLowOrderLDGenerator rates) t).mulVec initial none = 1 := by
    rw [matrixExponential_mulVec_apply_of_row_zero (augmentedLowOrderLDGenerator rates) t
      initial none fun _ ↦ rfl, hinitial]
  refine hasDerivAt_pi.mpr fun row ↦ ?_
  have hrow := hasDerivAt_pi.mp horbit (some (oneDemeCoordinate row))
  rw [augmentedGenerator_mulVec_oneDeme, hnone, mul_one] at hrow
  exact hrow

/-! ## The realizable set of NOTE1 (14) -/

/-- The vectors `(H, DD, Dz, pi2)` of NOTE1 (14) whose locus-exchangeable embedding, with
affine coordinate one and right-locus heterozygosity equal to the stored one, lies in the
enlarged one-deme realization body. -/
def oneDemeRealizableSet : Set (Fin 4 → ℝ) :=
  {vector | embedLowOrderLDState (oneDemeLift vector)
    ∈ realizationBody (EnlargedLowOrderLDGenerator.enlargedLowOrderLDFeature (D := 1))}

/-- The realizable set is convex: the embedded lift is affine in the vector and the enlarged
body is convex. -/
theorem convex_oneDemeRealizableSet : Convex ℝ oneDemeRealizableSet := by
  intro first hfirst second hsecond a b ha hb hab
  have hcombination : embedLowOrderLDState (oneDemeLift (a • first + b • second))
      = a • embedLowOrderLDState (oneDemeLift first)
        + b • embedLowOrderLDState (oneDemeLift second) := by
    funext coordinate
    simp only [embedLowOrderLDState, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    cases EnlargedLowOrderLDGenerator.storedSource coordinate with
    | none =>
      simp only [oneDemeLift]
      linarith
    | some stored => simp only [oneDemeLift, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  show embedLowOrderLDState (oneDemeLift (a • first + b • second))
    ∈ realizationBody (EnlargedLowOrderLDGenerator.enlargedLowOrderLDFeature (D := 1))
  rw [hcombination]
  exact convex_realizationBody _ hfirst hsecond ha hb hab

/-- The realizable set is closed: it is the preimage of the closed enlarged body under a
continuous map. -/
theorem isClosed_oneDemeRealizableSet : IsClosed oneDemeRealizableSet := by
  have hcontinuous : Continuous fun vector : Fin 4 → ℝ ↦
      embedLowOrderLDState (oneDemeLift vector) := by
    refine continuous_pi fun coordinate ↦ ?_
    simp only [embedLowOrderLDState]
    cases EnlargedLowOrderLDGenerator.storedSource coordinate with
    | none => exact (continuous_const : Continuous fun _ : Fin 4 → ℝ ↦ (1 : ℝ))
    | some stored => exact continuous_apply (oneDemeCoordinateEquiv.symm stored)
  exact (EnlargedBodyClosedness.isClosed_enlargedRealizationBody 1).preimage hcontinuous

/-- The realizable set is bounded: every coordinate of a vector in it is a coordinate of a
point of the compact enlarged body. -/
theorem isBounded_oneDemeRealizableSet : Bornology.IsBounded oneDemeRealizableSet := by
  obtain ⟨bound, hbound⟩ := isBounded_iff_forall_norm_le.mp
    (EnlargedBodyClosedness.isCompact_enlargedRealizationBody 1).isBounded
  refine isBounded_iff_forall_norm_le.mpr ⟨bound, fun vector hvector ↦ ?_⟩
  have hnorm := hbound (embedLowOrderLDState (oneDemeLift vector)) hvector
  refine (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans hnorm)).mpr fun row ↦ ?_
  have hentry : embedLowOrderLDState (oneDemeLift vector)
      (some (.inl (oneDemeCoordinateEquiv row))) = vector row := by
    show vector (oneDemeCoordinateEquiv.symm (oneDemeCoordinateEquiv row)) = vector row
    rw [Equiv.symm_apply_apply]
  rw [← hentry]
  exact (norm_le_pi_norm _ _).trans hnorm

/-! ## The orbit stays realizable -/

/-- The one-deme haplotype-frequency state in which every chromosome carries the `AB`
haplotype. Both loci are monomorphic, so the left- and right-locus heterozygosities agree. -/
def abHaplotypeState : TwoLocusHaplotypeFrequencies where
  AB := 1
  Ab := 0
  aB := 0
  ab := 0
  AB_nonneg := zero_le_one
  Ab_nonneg := le_rfl
  aB_nonneg := le_rfl
  ab_nonneg := le_rfl
  total_eq_one := by norm_num

/-- The embedding of the stored feature vector of `abHaplotypeState` is its enlarged feature
vector: the right-locus heterozygosity coordinate agrees with the stored heterozygosity
because both loci are monomorphic. -/
theorem embed_lowOrderLDFeature_abHaplotypeState :
    embedLowOrderLDState (lowOrderLDFeature 1 fun _ ↦ abHaplotypeState)
      = EnlargedLowOrderLDGenerator.enlargedLowOrderLDFeature fun _ ↦ abHaplotypeState := by
  funext coordinate
  cases coordinate with
  | none => rfl
  | some enlarged =>
    cases enlarged with
    | inl stored => rfl
    | inr pair =>
      show twoLocusJetMoment (fun _ ↦ abHaplotypeState) (.H pair.1 pair.2)
        = twoLocusRightHeterozygosity abHaplotypeState abHaplotypeState
      simp only [twoLocusJetMoment, twoLocusCoordinateJet, twoLocusHJet_value]
      norm_num [twoLocusLeftHeterozygosity, twoLocusRightHeterozygosity,
        TwoLocusHaplotypeFrequencies.leftFrequency, TwoLocusHaplotypeFrequencies.rightFrequency,
        abHaplotypeState]

/-- **The one-deme orbit stays realizable.** Started from the stored feature vector of
`abHaplotypeState`, the exact one-deme orbit has its `(H, DD, Dz, pi2)` coordinates in the
realizable set at every nonnegative time: the enlarged propagator intertwines with the
embedding and carries the closed enlarged body into itself.
Assumes: a microscopic approximation of the enlarged one-deme generator, supplied as data. -/
theorem oneDemeOrbit_mem_oneDemeRealizableSet {Branch : Type*} [Fintype Branch]
    (rates : ManyDemeLDRates 1)
    (approximation : MicroscopicApproximation (B := Branch)
      (EnlargedLowOrderLDGenerator.enlargedLowOrderLDFeature (D := 1))
      (enlargedLowOrderLDGenerator rates))
    (t : ℝ) (ht : 0 ≤ t) :
    oneDemeProjection ((matrixExponential (augmentedLowOrderLDGenerator rates) t).mulVec
        (lowOrderLDFeature 1 fun _ ↦ abHaplotypeState)) ∈ oneDemeRealizableSet := by
  have hnone : (matrixExponential (augmentedLowOrderLDGenerator rates) t).mulVec
      (lowOrderLDFeature 1 fun _ ↦ abHaplotypeState) none = 1 :=
    matrixExponential_mulVec_apply_of_row_zero (augmentedLowOrderLDGenerator rates) t
      (lowOrderLDFeature 1 fun _ ↦ abHaplotypeState) none fun _ ↦ rfl
  show embedLowOrderLDState (oneDemeLift (oneDemeProjection
      ((matrixExponential (augmentedLowOrderLDGenerator rates) t).mulVec
        (lowOrderLDFeature 1 fun _ ↦ abHaplotypeState))))
    ∈ realizationBody (EnlargedLowOrderLDGenerator.enlargedLowOrderLDFeature (D := 1))
  rw [oneDemeLift_oneDemeProjection _ hnone, ← enlargedPropagator_mulVec_embed,
    embed_lowOrderLDFeature_abHaplotypeState]
  exact EnlargedBodyClosedness.enlargedPropagator_mulVec_mem_of_approx rates approximation t ht
    _ (mem_realizationBody_of_range _ _)

/-! ## NOTE1 Theorem 3 -/

/-- The corpus stationary vector of NOTE1 (16) is the projection of the corpus closed-form
stationary low-order state. -/
theorem oneDemeStationaryVector_eq_oneDemeProjection (rates : ManyDemeLDRates 1) :
    oneDemeStationaryVector rates
      = oneDemeProjection (oneDemeStationaryLowOrderLDState rates) := by
  funext row
  fin_cases row <;> rfl

/-- **NOTE1 Theorem 3, the enlarged body form.** The locus-exchangeable embedding of the corpus
one-deme stationary low-order state lies in the enlarged realization body. The orbit of
`abHaplotypeState` solves the affine system (14) and stays in the closed, convex, bounded
realizable set, so the Cesàro limit places the unique stationary vector there too.
Assumes: a microscopic approximation of the enlarged one-deme generator, supplied as data. -/
theorem embed_oneDemeStationaryLowOrderLDState_mem_of_approx {Branch : Type*}
    [Fintype Branch] (rates : ManyDemeLDRates 1)
    (approximation : MicroscopicApproximation (B := Branch)
      (EnlargedLowOrderLDGenerator.enlargedLowOrderLDFeature (D := 1))
      (enlargedLowOrderLDGenerator rates)) :
    embedLowOrderLDState (oneDemeStationaryLowOrderLDState rates)
      ∈ realizationBody (EnlargedLowOrderLDGenerator.enlargedLowOrderLDFeature (D := 1)) := by
  have hvector : oneDemeStationaryVector rates ∈ oneDemeRealizableSet :=
    oneDemeStationaryVector_mem_of_orbit_mem rates oneDemeRealizableSet
      convex_oneDemeRealizableSet isClosed_oneDemeRealizableSet isBounded_oneDemeRealizableSet
      (fun time ↦ oneDemeProjection
        ((matrixExponential (augmentedLowOrderLDGenerator rates) time).mulVec
          (lowOrderLDFeature 1 fun _ ↦ abHaplotypeState)))
      (hasDerivAt_oneDemeOrbit rates (lowOrderLDFeature 1 fun _ ↦ abHaplotypeState) rfl)
      (oneDemeOrbit_mem_oneDemeRealizableSet rates approximation)
  rw [oneDemeStationaryVector_eq_oneDemeProjection] at hvector
  have hmember : embedLowOrderLDState
      (oneDemeLift (oneDemeProjection (oneDemeStationaryLowOrderLDState rates)))
      ∈ realizationBody (EnlargedLowOrderLDGenerator.enlargedLowOrderLDFeature (D := 1)) :=
    hvector
  rwa [oneDemeLift_oneDemeProjection (oneDemeStationaryLowOrderLDState rates) rfl]
    at hmember

/-- **NOTE1 Theorem 3.** The corpus one-deme stationary low-order state carries a
locus-exchangeable haplotype realization: one common probability law on the haplotype simplex
whose moments are all of its coordinates, with the expected left- and right-locus
heterozygosities equal.
Assumes: a microscopic approximation of the enlarged one-deme generator, supplied as data. -/
theorem nonempty_stationaryLocusExchangeableRealization_of_approx {Branch : Type*}
    [Fintype Branch] (rates : ManyDemeLDRates 1)
    (approximation : MicroscopicApproximation (B := Branch)
      (EnlargedLowOrderLDGenerator.enlargedLowOrderLDFeature (D := 1))
      (enlargedLowOrderLDGenerator rates)) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
      (oneDemeStationaryLowOrderLDState rates)) :=
  TwoLocusRealizabilityPreservation.nonempty_locusExchangeableRealization_of_embed_mem
    (embed_oneDemeStationaryLowOrderLDState_mem_of_approx rates approximation)

/-- The corpus one-deme stationary low-order state lies in the stored realization body, so
every inequality valid on that body holds at the ancestral boundary.
Assumes: a microscopic approximation of the enlarged one-deme generator, supplied as data. -/
theorem oneDemeStationaryLowOrderLDState_mem_realizationBody_of_approx {Branch : Type*}
    [Fintype Branch] (rates : ManyDemeLDRates 1)
    (approximation : MicroscopicApproximation (B := Branch)
      (EnlargedLowOrderLDGenerator.enlargedLowOrderLDFeature (D := 1))
      (enlargedLowOrderLDGenerator rates)) :
    oneDemeStationaryLowOrderLDState rates ∈ realizationBody (lowOrderLDFeature 1) := by
  obtain ⟨realization⟩ :=
    nonempty_stationaryLocusExchangeableRealization_of_approx rates approximation
  exact KernelRealizationPreservation.lowOrderLDState_mem_realizationBody_of_realization
    realization.toLowOrderLDHaplotypeRealization

end

end Descent.Portability.StationaryHaplotypeRealization
