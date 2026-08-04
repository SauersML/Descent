/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Calibrator

/-!
# Near-optimal geometry under landscape superposition

This file formalizes the exact level-resolved decomposition that governs overlap-gap
persistence under a positive superposition of finite landscapes.  It deliberately separates
the easy direction from the hard one:

* `nearOptimal_superposition_iff_exists_levels` is an equality of configuration sets;
* `superposedAchievableOverlap_subset_levelResolved` is the induced one-sided inclusion for
  achievable overlaps;
* `forbiddenOverlap_of_levelResolved_cover` and
  `forbiddenInterval_of_levelResolved_cover` certify persistence of a forbidden overlap or
  interval;
* no converse is asserted.  Dissolution requires constructing common configurations and does
  not follow from this set calculus.

The final section checks the polynomial arithmetic behind the spherical calibration example.
It proves that each idiosyncratic tail has a negative endpoint certificate while their
half-weight covariance mixture has a strictly positive certificate throughout `[0, 1]`.
No external spin-glass criterion is accepted as a theorem parameter; only the polynomial fact
that such a criterion would consume is formalized here.
-/

open scoped BigOperators Matrix

section LevelResolvedCalculus

variable {Index Config Overlap : Type*} [Fintype Index]

/-- Positive linear superposition of component landscapes. -/
noncomputable def superposedLandscape
    (weight : Index → ℝ) (energy : Index → Config → ℝ) (config : Config) : ℝ :=
  ∑ k, weight k * energy k config

/-- Configurations above an energy level. -/
def NearOptimalSet (energy : Config → ℝ) (level : ℝ) : Set Config :=
  {config | level ≤ energy config}

/-- A vector of component levels whose weighted value reaches the superposed target. -/
def AdmissibleLevels (weight : Index → ℝ) (target : ℝ) (level : Index → ℝ) : Prop :=
  target ≤ ∑ k, weight k * level k

/-- **Exact near-optimal-set decomposition.**  A configuration is superposed-near-optimal iff
it lies above some admissible vector of component levels.  Nonnegative weights are precisely
what makes the reverse implication valid. -/
theorem nearOptimal_superposition_iff_exists_levels
    (weight : Index → ℝ) (energy : Index → Config → ℝ) (target : ℝ)
    (hweight : ∀ k, 0 ≤ weight k) (config : Config) :
    config ∈ NearOptimalSet (superposedLandscape weight energy) target ↔
      ∃ level : Index → ℝ,
        AdmissibleLevels weight target level ∧
          ∀ k, config ∈ NearOptimalSet (energy k) (level k) := by
  constructor
  · intro hconfig
    refine ⟨fun k ↦ energy k config, hconfig, ?_⟩
    intro k
    change energy k config ≤ energy k config
    exact le_rfl
  · rintro ⟨level, hadmissible, hlevel⟩
    exact hadmissible.trans <| Finset.sum_le_sum fun k hk ↦
      mul_le_mul_of_nonneg_left (show level k ≤ energy k config from hlevel k) (hweight k)

/-- Overlaps achieved by a common pair of configurations above two component-level vectors. -/
def ComponentAchievableOverlaps
    (energy : Index → Config → ℝ) (overlap : Config → Config → Overlap)
    (leftLevel rightLevel : Index → ℝ) (k : Index) : Set Overlap :=
  {q | ∃ left right : Config,
    left ∈ NearOptimalSet (energy k) (leftLevel k) ∧
      right ∈ NearOptimalSet (energy k) (rightLevel k) ∧ overlap left right = q}

/-- Overlaps achieved by pairs above the superposed target. -/
def SuperposedAchievableOverlaps
    (weight : Index → ℝ) (energy : Index → Config → ℝ)
    (overlap : Config → Config → Overlap) (target : ℝ) : Set Overlap :=
  {q | ∃ left right : Config,
    left ∈ NearOptimalSet (superposedLandscape weight energy) target ∧
      right ∈ NearOptimalSet (superposedLandscape weight energy) target ∧
      overlap left right = q}

/-- **Universal inclusion for achievable overlaps.**  Every overlap of a superposed-near-optimal
pair belongs simultaneously to every component's achievable set at some two admissible level
vectors.  The component witnesses on the right may differ, so this is only an inclusion. -/
theorem superposedAchievableOverlap_subset_levelResolved
    (weight : Index → ℝ) (energy : Index → Config → ℝ)
    (overlap : Config → Config → Overlap) (target : ℝ)
    (hweight : ∀ k, 0 ≤ weight k) (q : Overlap)
    (hq : q ∈ SuperposedAchievableOverlaps weight energy overlap target) :
    ∃ leftLevel rightLevel : Index → ℝ,
      AdmissibleLevels weight target leftLevel ∧
        AdmissibleLevels weight target rightLevel ∧
          ∀ k, q ∈ ComponentAchievableOverlaps energy overlap leftLevel rightLevel k := by
  rcases hq with ⟨left, right, hleft, hright, hoverlap⟩
  rw [nearOptimal_superposition_iff_exists_levels weight energy target hweight left] at hleft
  rw [nearOptimal_superposition_iff_exists_levels weight energy target hweight right] at hright
  rcases hleft with ⟨leftLevel, hleftAdmissible, hleftLevel⟩
  rcases hright with ⟨rightLevel, hrightAdmissible, hrightLevel⟩
  refine ⟨leftLevel, rightLevel, hleftAdmissible, hrightAdmissible, ?_⟩
  intro k
  exact ⟨left, right, hleftLevel k, hrightLevel k, hoverlap⟩

/-- A level-resolved cover by component forbidden sets certifies a forbidden overlap for the
superposition.  This is the rigorous persistence direction. -/
theorem forbiddenOverlap_of_levelResolved_cover
    (weight : Index → ℝ) (energy : Index → Config → ℝ)
    (overlap : Config → Config → Overlap) (target : ℝ)
    (hweight : ∀ k, 0 ≤ weight k) (q : Overlap)
    (hcover : ∀ leftLevel rightLevel,
      AdmissibleLevels weight target leftLevel →
        AdmissibleLevels weight target rightLevel →
          ∃ k, q ∉ ComponentAchievableOverlaps energy overlap leftLevel rightLevel k) :
    q ∉ SuperposedAchievableOverlaps weight energy overlap target := by
  intro hq
  rcases superposedAchievableOverlap_subset_levelResolved
      weight energy overlap target hweight q hq with
    ⟨leftLevel, rightLevel, hleft, hright, hall⟩
  rcases hcover leftLevel rightLevel hleft hright with ⟨k, hk⟩
  exact hk (hall k)

/-- Interval version of the persistence theorem.  The order on overlaps is used only to name the
candidate interval; the proof is pointwise. -/
theorem forbiddenInterval_of_levelResolved_cover
    [LinearOrder Overlap]
    (weight : Index → ℝ) (energy : Index → Config → ℝ)
    (overlap : Config → Config → Overlap) (target : ℝ)
    (hweight : ∀ k, 0 ≤ weight k) (lower upper : Overlap)
    (hcover : ∀ q ∈ Set.Ioo lower upper, ∀ leftLevel rightLevel,
      AdmissibleLevels weight target leftLevel →
        AdmissibleLevels weight target rightLevel →
          ∃ k, q ∉ ComponentAchievableOverlaps energy overlap leftLevel rightLevel k) :
    Set.Ioo lower upper ⊆
      (SuperposedAchievableOverlaps weight energy overlap target)ᶜ := by
  intro q hq
  exact forbiddenOverlap_of_levelResolved_cover weight energy overlap target hweight q
    (hcover q hq)

end LevelResolvedCalculus

/-! ## Boundary of the simplex -/

section SimplexBoundary

variable {Index Config : Type*} [Fintype Index] [DecidableEq Index]

/-- A simplex vertex selecting one component landscape. -/
noncomputable def oneHotWeight (selected : Index) (k : Index) : ℝ :=
  if k = selected then 1 else 0

/-- At a simplex vertex the superposition is exactly the selected landscape. -/
theorem superposedLandscape_oneHot
    (energy : Index → Config → ℝ) (selected : Index) (config : Config) :
    superposedLandscape (oneHotWeight selected) energy config = energy selected config := by
  classical
  unfold superposedLandscape oneHotWeight
  rw [Finset.sum_eq_single selected]
  · simp
  · intro k hk hne
    simp [hne]
  · simp

/-- Consequently the near-optimal set at a simplex vertex is the component near-optimal set.
Any statement claiming uniform destruction up to the boundary must therefore fail. -/
theorem nearOptimalSet_superposition_oneHot
    (energy : Index → Config → ℝ) (selected : Index) (target : ℝ) :
    NearOptimalSet (superposedLandscape (oneHotWeight selected) energy) target =
      NearOptimalSet (energy selected) target := by
  ext config
  simp only [NearOptimalSet, Set.mem_setOf_eq, superposedLandscape_oneHot]

end SimplexBoundary

/-! ## Band migration is compatible with disjoint endpoints -/

/-- A unit-width forbidden band whose center moves linearly across the overlap line. -/
def migratingForbiddenBand (mix : ℝ) : Set ℝ :=
  Set.Ioo (2 * mix) (2 * mix + 1)

/-- The endpoint bands are disjoint. -/
theorem migratingForbiddenBand_endpoints_disjoint :
    Disjoint (migratingForbiddenBand 0) (migratingForbiddenBand 1) := by
  rw [Set.disjoint_left]
  intro q hleft hright
  rcases hleft with ⟨hleftLower, hleftUpper⟩
  rcases hright with ⟨hrightLower, hrightUpper⟩
  norm_num at hleftLower hleftUpper hrightLower hrightUpper
  linarith

/-- Nevertheless every point of the interpolation path has a nonempty forbidden band.  Thus
endpoint disjointness and continuity alone cannot imply gap dissolution: a band may migrate. -/
theorem migratingForbiddenBand_nonempty (mix : ℝ) :
    (migratingForbiddenBand mix).Nonempty := by
  refine ⟨2 * mix + 1 / 2, ?_⟩
  constructor <;> norm_num

/-! ## Spherical covariance calibration arithmetic -/

/-- Even mixed spherical covariance with a shared quadratic component and two tail terms. -/
noncomputable def mixedSphericalCovariance (alpha beta q : ℝ) : ℝ :=
  q ^ 2 + alpha * q ^ 4 + beta * q ^ 6

/-- Independent half-weight superposition adds covariances with squared weights.  The shared
quadratic component is retained, whereas the two idiosyncratic tails are each diluted by one
half. -/
theorem halfWeight_quartic_sextic_covariance (q : ℝ) :
    (1 / 2 : ℝ) * mixedSphericalCovariance (1 / 10) 0 q +
        (1 / 2 : ℝ) * mixedSphericalCovariance 0 (1 / 14) q =
      mixedSphericalCovariance (1 / 20) (1 / 28) q := by
  unfold mixedSphericalCovariance
  ring

/-- The polynomial certificate `2 ξ'' ξ'''' - 3 (ξ''')²` for
`ξ(q) = q² + alpha q⁴ + beta q⁶`. -/
noncomputable def sphericalGaplessnessCertificate (alpha beta q : ℝ) : ℝ :=
  2 * (2 + 12 * alpha * q ^ 2 + 30 * beta * q ^ 4) *
      (24 * alpha + 360 * beta * q ^ 2) -
    3 * (24 * alpha * q + 120 * beta * q ^ 3) ^ 2

/-- The `q⁴` summand's endpoint certificate is negative. -/
theorem quarticTail_certificate_at_one_neg :
    sphericalGaplessnessCertificate (1 / 10) 0 1 < 0 := by
  norm_num [sphericalGaplessnessCertificate]

/-- The `q⁶` summand's endpoint certificate is negative. -/
theorem sexticTail_certificate_at_one_neg :
    sphericalGaplessnessCertificate 0 (1 / 14) 1 < 0 := by
  norm_num [sphericalGaplessnessCertificate]

/-- After half-weight covariance superposition, the common quadratic component retains full
strength while each idiosyncratic tail is halved.  The resulting certificate is strictly
positive on the full overlap interval. -/
theorem dilutedTails_certificate_pos (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 < sphericalGaplessnessCertificate (1 / 20) (1 / 28) q := by
  have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
  have hq2le : q ^ 2 ≤ 1 := by nlinarith
  have hq4le : q ^ 4 ≤ q ^ 2 := by nlinarith [sq_nonneg (q ^ 2)]
  have hq6le : q ^ 6 ≤ q ^ 2 := by
    have hq4nonneg : 0 ≤ q ^ 4 := by nlinarith [sq_nonneg (q ^ 2)]
    calc
      q ^ 6 = q ^ 4 * q ^ 2 := by ring
      _ ≤ q ^ 4 * 1 := mul_le_mul_of_nonneg_left hq2le hq4nonneg
      _ ≤ q ^ 2 := by simpa using hq4le
  unfold sphericalGaplessnessCertificate
  nlinarith

/-! ## Anisotropy separates Euclidean overlap from covariance energy -/

abbrev TwoCoordinateConfiguration := Fin 2 → ℝ

/-- Euclidean overlap, the coordinate used by the classical isotropic band calculation. -/
noncomputable def configurationOverlap
    (left right : TwoCoordinateConfiguration) : ℝ :=
  dotProduct left right

/-- Energy scale of the displacement from a planted configuration under covariance `sigma`. -/
noncomputable def covarianceDisplacementEnergy
    (sigma : Matrix (Fin 2) (Fin 2) ℝ)
    (candidate truth : TwoCoordinateConfiguration) : ℝ :=
  dotProduct (candidate - truth) (sigma.mulVec (candidate - truth))

/-- A positive anisotropic covariance with eigen-directions rotated relative to coordinates. -/
noncomputable def overlapEnergyWitnessCovariance : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2, 1; 1, 2]

/-- The covariance energy is a sum of three squares. -/
theorem overlapEnergyWitnessCovariance_energy_eq (vector : TwoCoordinateConfiguration) :
    dotProduct vector (overlapEnergyWitnessCovariance.mulVec vector) =
      vector 0 ^ 2 + vector 1 ^ 2 + (vector 0 + vector 1) ^ 2 := by
  simp [overlapEnergyWitnessCovariance, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- The witness covariance is strictly positive on every nonzero configuration. -/
theorem overlapEnergyWitnessCovariance_pos
    (vector : TwoCoordinateConfiguration) (hvector : vector ≠ 0) :
    0 < dotProduct vector (overlapEnergyWitnessCovariance.mulVec vector) := by
  rw [overlapEnergyWitnessCovariance_energy_eq]
  have hcoordinate : vector 0 ≠ 0 ∨ vector 1 ≠ 0 := by
    by_contra hzero
    push_neg at hzero
    apply hvector
    funext i
    fin_cases i
    · exact hzero.1
    · exact hzero.2
  rcases hcoordinate with hfirst | hsecond
  · nlinarith [sq_pos_of_ne_zero hfirst, sq_nonneg (vector 1),
      sq_nonneg (vector 0 + vector 1)]
  · nlinarith [sq_nonneg (vector 0), sq_pos_of_ne_zero hsecond,
      sq_nonneg (vector 0 + vector 1)]

noncomputable def overlapEnergyTruth : TwoCoordinateConfiguration := ![1, 0]
noncomputable def overlapEnergyPositive : TwoCoordinateConfiguration := ![0, 1]
noncomputable def overlapEnergyNegative : TwoCoordinateConfiguration := ![0, -1]

/-- The two candidates have the same Euclidean norm and the same overlap with the planted
configuration, but different covariance energies.  Thus an anisotropic first-moment theory
cannot project to overlap alone; its state space must retain both `(ρ, r)`. -/
theorem equal_overlap_different_covariance_energy :
    configurationOverlap overlapEnergyPositive overlapEnergyTruth = 0 ∧
      configurationOverlap overlapEnergyNegative overlapEnergyTruth = 0 ∧
      configurationOverlap overlapEnergyPositive overlapEnergyPositive = 1 ∧
      configurationOverlap overlapEnergyNegative overlapEnergyNegative = 1 ∧
      covarianceDisplacementEnergy overlapEnergyWitnessCovariance
          overlapEnergyPositive overlapEnergyTruth = 2 ∧
      covarianceDisplacementEnergy overlapEnergyWitnessCovariance
          overlapEnergyNegative overlapEnergyTruth = 6 := by
  norm_num [configurationOverlap, covarianceDisplacementEnergy,
    overlapEnergyWitnessCovariance, overlapEnergyTruth, overlapEnergyPositive,
    overlapEnergyNegative, dotProduct, Matrix.mulVec, Fin.sum_univ_two]

end Calibrator
